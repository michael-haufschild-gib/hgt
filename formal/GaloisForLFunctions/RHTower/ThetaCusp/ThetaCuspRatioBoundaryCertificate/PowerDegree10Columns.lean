import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.FullPowerRows

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryRePowerRow77_0Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-230981303/816293376 : ℝ)) ((22-0)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-14198581679/58773123072 : ℝ)) ((22-0)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((1259320357/44079842304 : ℝ)) ((22-0)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((343884160085/12694994583552 : ℝ)) ((22-0)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_0Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_0Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_0Degree10Chunk0 x=boundaryRePowerRow77_0Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_0Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((3398669372467/10968475320188928 : ℝ)) ((22-0)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-2383866633305/4113178245070848 : ℝ)) ((22-0)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((-15566885473627/444223250467651584 : ℝ)) ((22-0)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((77095760617/15617223649253376 : ℝ)) ((22-0)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_0Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_0Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_0Degree10Chunk4 x=boundaryRePowerRow77_0Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_0Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((42854922195427/71964166575759556608 : ℝ)) ((22-0)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-3583883340325/80959687397729501184 : ℝ)) ((22-0)+2*9-6) 0 9 10 x))

def boundaryRePowerRow77_0Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_0Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_0Degree10Chunk8 x=boundaryRePowerRow77_0Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_0Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_0 10 x=c} := by

  have he : boundaryRePowerRow77_0 10 x=((boundaryRePowerRow77_0Degree10Chunk0 x) + ((boundaryRePowerRow77_0Degree10Chunk4 x) + (boundaryRePowerRow77_0Degree10Chunk8 x))) := by

    dsimp only [boundaryRePowerRow77_0,boundaryRePowerRow77_0Degree10Chunk0,boundaryRePowerRow77_0Degree10Chunk4,boundaryRePowerRow77_0Degree10Chunk8]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_0Degree10Chunk0Norm x).property,(boundaryRePowerRow77_0Degree10Chunk4Norm x).property,(boundaryRePowerRow77_0Degree10Chunk8Norm x).property]

    dsimp only [boundaryRePowerRow77_0Degree10Chunk0Norm,boundaryRePowerRow77_0Degree10Chunk4Norm,boundaryRePowerRow77_0Degree10Chunk8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_1Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-324249763/45349632 : ℝ)) ((22-1)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-167201743973/58773123072 : ℝ)) ((22-1)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((6187558971961/4231664861184 : ℝ)) ((22-1)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((7863700323469/25389989167104 : ℝ)) ((22-1)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_1Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_1Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_1Degree10Chunk0 x=boundaryRePowerRow77_1Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_1Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_1Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-116766132507617/2437438960041984 : ℝ)) ((22-1)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-1145421589780511/197432555763400704 : ℝ)) ((22-1)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((206177013717469/222111625233825792 : ℝ)) ((22-1)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((54630215066029/888446500935303168 : ℝ)) ((22-1)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_1Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_1Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_1Degree10Chunk4 x=boundaryRePowerRow77_1Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_1Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_1Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-3134120843656637/143928333151519113216 : ℝ)) ((22-1)+2*8-6) 0 8 10 x) + ((boundaryTermPowerRow77 ((240050053994077/143928333151519113216 : ℝ)) ((22-1)+2*9-6) 0 9 10 x) + (boundaryTermPowerRow77 ((-219554668799417/5829097492636524085248 : ℝ)) ((22-1)+2*10-6) 0 10 10 x)))

def boundaryRePowerRow77_1Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_1Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_1Degree10Chunk8 x=boundaryRePowerRow77_1Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_1Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_1Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_1 10 x=c} := by

  have he : boundaryRePowerRow77_1 10 x=((boundaryRePowerRow77_1Degree10Chunk0 x) + ((boundaryRePowerRow77_1Degree10Chunk4 x) + (boundaryRePowerRow77_1Degree10Chunk8 x))) := by

    dsimp only [boundaryRePowerRow77_1,boundaryRePowerRow77_1Degree10Chunk0,boundaryRePowerRow77_1Degree10Chunk4,boundaryRePowerRow77_1Degree10Chunk8]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_1Degree10Chunk0Norm x).property,(boundaryRePowerRow77_1Degree10Chunk4Norm x).property,(boundaryRePowerRow77_1Degree10Chunk8Norm x).property]

    dsimp only [boundaryRePowerRow77_1Degree10Chunk0Norm,boundaryRePowerRow77_1Degree10Chunk4Norm,boundaryRePowerRow77_1Degree10Chunk8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_2Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-17013304387/272097792 : ℝ)) ((22-2)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((38431147015/7346640384 : ℝ)) ((22-2)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((61220920127935/4231664861184 : ℝ)) ((22-2)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-276330887018353/304679870005248 : ℝ)) ((22-2)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_2Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_2Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_2Degree10Chunk0 x=boundaryRePowerRow77_2Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_2Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-1905102852670427/5484237660094464 : ℝ)) ((22-2)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((62486563359189029/789730223053602816 : ℝ)) ((22-2)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((892127151386231/1579460446107205632 : ℝ)) ((22-2)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-555318049108146761/255872592269367312384 : ℝ)) ((22-2)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_2Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_2Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_2Degree10Chunk4 x=boundaryRePowerRow77_2Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_2Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((7203123035673985/23988055525253185536 : ℝ)) ((22-2)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-12468472096182551/647677499181836009472 : ℝ)) ((22-2)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((17574827696587321/31088519960728128454656 : ℝ)) ((22-2)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-2092690629306389/559593359293106312183808 : ℝ)) ((22-2)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_2Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_2Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_2Degree10Chunk8 x=boundaryRePowerRow77_2Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_2Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_2 10 x=c} := by

  have he : boundaryRePowerRow77_2 10 x=((boundaryRePowerRow77_2Degree10Chunk0 x) + ((boundaryRePowerRow77_2Degree10Chunk4 x) + (boundaryRePowerRow77_2Degree10Chunk8 x))) := by

    dsimp only [boundaryRePowerRow77_2,boundaryRePowerRow77_2Degree10Chunk0,boundaryRePowerRow77_2Degree10Chunk4,boundaryRePowerRow77_2Degree10Chunk8]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_2Degree10Chunk0Norm x).property,(boundaryRePowerRow77_2Degree10Chunk4Norm x).property,(boundaryRePowerRow77_2Degree10Chunk8Norm x).property]

    dsimp only [boundaryRePowerRow77_2Degree10Chunk0Norm,boundaryRePowerRow77_2Degree10Chunk4Norm,boundaryRePowerRow77_2Degree10Chunk8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_3Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-255401548/1594323 : ℝ)) ((22-3)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((459665122079/2448880128 : ℝ)) ((22-3)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((24735163810307/1410554953728 : ℝ)) ((22-3)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-3984197611531409/304679870005248 : ℝ)) ((22-3)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_3Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_3Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_3Degree10Chunk0 x=boundaryRePowerRow77_3Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_3Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((21192601872574421/7312316880125952 : ℝ)) ((22-3)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((30446098602014515/789730223053602816 : ℝ)) ((22-3)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((-128178562347826931/1184595334580404224 : ℝ)) ((22-3)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((35336490088500240085/2046980738154938499072 : ℝ)) ((22-3)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_3Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_3Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_3Degree10Chunk4 x=boundaryRePowerRow77_3Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_3Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-8067016470465992459/6140942214464815497216 : ℝ)) ((22-3)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((4590822519085866529/82902719895275009212416 : ℝ)) ((22-3)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((-1083704430860289001/746124479057475082911744 : ℝ)) ((22-3)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((30695821105674067/4476746874344850497470464 : ℝ)) ((22-3)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_3Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_3Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_3Degree10Chunk8 x=boundaryRePowerRow77_3Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_3Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 ((13750076961227201/40290721869103654477234176 : ℝ)) ((22-3)+2*12-6) 0 12 10 x)

def boundaryRePowerRow77_3Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_3Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_3Degree10Chunk12 x=boundaryRePowerRow77_3Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_3Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_3 10 x=c} := by

  have he : boundaryRePowerRow77_3 10 x=(((boundaryRePowerRow77_3Degree10Chunk0 x) + (boundaryRePowerRow77_3Degree10Chunk4 x)) + ((boundaryRePowerRow77_3Degree10Chunk8 x) + (boundaryRePowerRow77_3Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_3,boundaryRePowerRow77_3Degree10Chunk0,boundaryRePowerRow77_3Degree10Chunk4,boundaryRePowerRow77_3Degree10Chunk8,boundaryRePowerRow77_3Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_3Degree10Chunk0Norm x).property,(boundaryRePowerRow77_3Degree10Chunk4Norm x).property,(boundaryRePowerRow77_3Degree10Chunk8Norm x).property,(boundaryRePowerRow77_3Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_3Degree10Chunk0Norm,boundaryRePowerRow77_3Degree10Chunk4Norm,boundaryRePowerRow77_3Degree10Chunk8Norm,boundaryRePowerRow77_3Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_4Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((580451074939/816293376 : ℝ)) ((22-4)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((3027591827663/4897760256 : ℝ)) ((22-4)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-872943112477597/4231664861184 : ℝ)) ((22-4)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((1082809371360415/25389989167104 : ℝ)) ((22-4)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_4Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_4Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_4Degree10Chunk0 x=boundaryRePowerRow77_4Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_4Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_4Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((103660301096665273/21936950640377856 : ℝ)) ((22-4)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-6349396462835622133/1579460446107205632 : ℝ)) ((22-4)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((17452969212118235473/28430288029929701376 : ℝ)) ((22-4)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-105209792018815952689/4093961476309876998144 : ℝ)) ((22-4)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_4Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_4Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_4Degree10Chunk4 x=boundaryRePowerRow77_4Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_4Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_4Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-793839895007146664479/294765226294311143866368 : ℝ)) ((22-4)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((468378633871040181617/1326443518324400147398656 : ℝ)) ((22-4)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((-172581908916053155805/11937991664919601326587904 : ℝ)) ((22-4)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((3639349364096350207/13430240623034551492411392 : ℝ)) ((22-4)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_4Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_4Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_4Degree10Chunk8 x=boundaryRePowerRow77_4Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_4Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_4Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-9905633421281934959/1933954649716975414907240448 : ℝ)) ((22-4)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((293575300609695167/8702795923726389367082582016 : ℝ)) ((22-4)+2*13-6) 0 13 10 x))

def boundaryRePowerRow77_4Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_4Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_4Degree10Chunk12 x=boundaryRePowerRow77_4Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_4Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_4Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_4 10 x=c} := by

  have he : boundaryRePowerRow77_4 10 x=(((boundaryRePowerRow77_4Degree10Chunk0 x) + (boundaryRePowerRow77_4Degree10Chunk4 x)) + ((boundaryRePowerRow77_4Degree10Chunk8 x) + (boundaryRePowerRow77_4Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_4,boundaryRePowerRow77_4Degree10Chunk0,boundaryRePowerRow77_4Degree10Chunk4,boundaryRePowerRow77_4Degree10Chunk8,boundaryRePowerRow77_4Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_4Degree10Chunk0Norm x).property,(boundaryRePowerRow77_4Degree10Chunk4Norm x).property,(boundaryRePowerRow77_4Degree10Chunk8Norm x).property,(boundaryRePowerRow77_4Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_4Degree10Chunk0Norm,boundaryRePowerRow77_4Degree10Chunk4Norm,boundaryRePowerRow77_4Degree10Chunk8Norm,boundaryRePowerRow77_4Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_5Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((641382265649/136048896 : ℝ)) ((22-5)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-42631093586323/58773123072 : ℝ)) ((22-5)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((24033298136159/264479053824 : ℝ)) ((22-5)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((25507776569387275/152339935002624 : ℝ)) ((22-5)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_5Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_5Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_5Degree10Chunk0 x=boundaryRePowerRow77_5Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_5Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-557960873325484405/5484237660094464 : ℝ)) ((22-5)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((7418330926261069049/526486815369068544 : ℝ)) ((22-5)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((38501327257187750557/113721152119718805504 : ℝ)) ((22-5)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-443037124184622331457/1364653825436625666048 : ℝ)) ((22-5)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_5Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_5Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_5Degree10Chunk4 x=boundaryRePowerRow77_5Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_5Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((8224411146406593623867/196510150862874095910912 : ℝ)) ((22-5)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-27106615414255252681223/10611548146595201179189248 : ℝ)) ((22-5)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((2510609098595788666727/31834644439785603537567744 : ℝ)) ((22-5)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-143524555414052015797/143255899979035215919054848 : ℝ)) ((22-5)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_5Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_5Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_5Degree10Chunk8 x=boundaryRePowerRow77_5Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_5Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((21237620319636992089/1933954649716975414907240448 : ℝ)) ((22-5)+2*12-6) 0 12 10 x) + ((boundaryTermPowerRow77 ((-4675098911177466233/23207455796603704978886885376 : ℝ)) ((22-5)+2*13-6) 0 13 10 x) + (boundaryTermPowerRow77 ((405506432602597781/626601306508300034429945905152 : ℝ)) ((22-5)+2*14-6) 0 14 10 x)))

def boundaryRePowerRow77_5Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_5Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_5Degree10Chunk12 x=boundaryRePowerRow77_5Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_5Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_5 10 x=c} := by

  have he : boundaryRePowerRow77_5 10 x=(((boundaryRePowerRow77_5Degree10Chunk0 x) + (boundaryRePowerRow77_5Degree10Chunk4 x)) + ((boundaryRePowerRow77_5Degree10Chunk8 x) + (boundaryRePowerRow77_5Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_5,boundaryRePowerRow77_5Degree10Chunk0,boundaryRePowerRow77_5Degree10Chunk4,boundaryRePowerRow77_5Degree10Chunk8,boundaryRePowerRow77_5Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_5Degree10Chunk0Norm x).property,(boundaryRePowerRow77_5Degree10Chunk4Norm x).property,(boundaryRePowerRow77_5Degree10Chunk8Norm x).property,(boundaryRePowerRow77_5Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_5Degree10Chunk0Norm,boundaryRePowerRow77_5Degree10Chunk4Norm,boundaryRePowerRow77_5Degree10Chunk8Norm,boundaryRePowerRow77_5Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_6Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((521984467501/90699264 : ℝ)) ((22-6)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-38296672442261/19591041024 : ℝ)) ((22-6)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((9044128743375011/4231664861184 : ℝ)) ((22-6)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-460923347021608217/304679870005248 : ℝ)) ((22-6)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_6Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_6Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_6Degree10Chunk0 x=boundaryRePowerRow77_6Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_6Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((3386468087123864579/21936950640377856 : ℝ)) ((22-6)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((31639773598267866541/789730223053602816 : ℝ)) ((22-6)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((-1534458378055478218519/113721152119718805504 : ℝ)) ((22-6)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((14056976992682328934859/8187922952619753996288 : ℝ)) ((22-6)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_6Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_6Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_6Degree10Chunk4 x=boundaryRePowerRow77_6Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_6Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-3849413208508757250629/36845653286788892983296 : ℝ)) ((22-6)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((13017708381092649189173/5305774073297600589594624 : ℝ)) ((22-6)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((3446520881208640473325/95503933319356810612703232 : ℝ)) ((22-6)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-1142267097772873945517/286511799958070431838109696 : ℝ)) ((22-6)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_6Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_6Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_6Degree10Chunk8 x=boundaryRePowerRow77_6Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_6Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((405734704255409069305/3867909299433950829814480896 : ℝ)) ((22-6)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-8390822305894903273/17405591847452778734165164032 : ℝ)) ((22-6)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((-949546426483032623/626601306508300034429945905152 : ℝ)) ((22-6)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((18285856292474113/5639411758574700309869513146368 : ℝ)) ((22-6)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_6Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_6Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_6Degree10Chunk12 x=boundaryRePowerRow77_6Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_6Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_6 10 x=c} := by

  have he : boundaryRePowerRow77_6 10 x=(((boundaryRePowerRow77_6Degree10Chunk0 x) + (boundaryRePowerRow77_6Degree10Chunk4 x)) + ((boundaryRePowerRow77_6Degree10Chunk8 x) + (boundaryRePowerRow77_6Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_6,boundaryRePowerRow77_6Degree10Chunk0,boundaryRePowerRow77_6Degree10Chunk4,boundaryRePowerRow77_6Degree10Chunk8,boundaryRePowerRow77_6Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_6Degree10Chunk0Norm x).property,(boundaryRePowerRow77_6Degree10Chunk4Norm x).property,(boundaryRePowerRow77_6Degree10Chunk8Norm x).property,(boundaryRePowerRow77_6Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_6Degree10Chunk0Norm,boundaryRePowerRow77_6Degree10Chunk4Norm,boundaryRePowerRow77_6Degree10Chunk8Norm,boundaryRePowerRow77_6Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_7Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-47837539691/8503056 : ℝ)) ((22-7)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((86019589412363/9795520512 : ℝ)) ((22-7)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-13018275535923361/1057916215296 : ℝ)) ((22-7)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-124219748680329659/304679870005248 : ℝ)) ((22-7)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_7Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_7Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_7Degree10Chunk0 x=boundaryRePowerRow77_7Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_7Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_7Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((13467142392276357361/10968475320188928 : ℝ)) ((22-7)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-253415598630830755853/789730223053602816 : ℝ)) ((22-7)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((2173733722472516133643/56860576059859402752 : ℝ)) ((22-7)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-9950442194462674810099/8187922952619753996288 : ℝ)) ((22-7)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_7Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_7Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_7Degree10Chunk4 x=boundaryRePowerRow77_7Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_7Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_7Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-112080901432557906299243/589530452588622287732736 : ℝ)) ((22-7)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((237165594725865884168879/10611548146595201179189248 : ℝ)) ((22-7)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((-96039386593052954438111/95503933319356810612703232 : ℝ)) ((22-7)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((1741471493734137984437/71627949989517607959527424 : ℝ)) ((22-7)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_7Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_7Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_7Degree10Chunk8 x=boundaryRePowerRow77_7Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_7Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_7Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-457041462381164301229/966977324858487707453620224 : ℝ)) ((22-7)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((347100065275036241875/69622367389811114936660656128 : ℝ)) ((22-7)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((-8234022588000933059/626601306508300034429945905152 : ℝ)) ((22-7)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((128030383508489/2819705879287350154934756573184 : ℝ)) ((22-7)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_7Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_7Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_7Degree10Chunk12 x=boundaryRePowerRow77_7Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_7Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_7Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 ((168937493305/49565142409347951942212517888 : ℝ)) ((22-7)+2*16-6) 0 16 10 x)

def boundaryRePowerRow77_7Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_7Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_7Degree10Chunk16 x=boundaryRePowerRow77_7Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_7Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_7Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_7 10 x=c} := by

  have he : boundaryRePowerRow77_7 10 x=(((boundaryRePowerRow77_7Degree10Chunk0 x) + (boundaryRePowerRow77_7Degree10Chunk4 x)) + ((boundaryRePowerRow77_7Degree10Chunk8 x) + ((boundaryRePowerRow77_7Degree10Chunk12 x) + (boundaryRePowerRow77_7Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_7,boundaryRePowerRow77_7Degree10Chunk0,boundaryRePowerRow77_7Degree10Chunk4,boundaryRePowerRow77_7Degree10Chunk8,boundaryRePowerRow77_7Degree10Chunk12,boundaryRePowerRow77_7Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_7Degree10Chunk0Norm x).property,(boundaryRePowerRow77_7Degree10Chunk4Norm x).property,(boundaryRePowerRow77_7Degree10Chunk8Norm x).property,(boundaryRePowerRow77_7Degree10Chunk12Norm x).property,(boundaryRePowerRow77_7Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_7Degree10Chunk0Norm,boundaryRePowerRow77_7Degree10Chunk4Norm,boundaryRePowerRow77_7Degree10Chunk8Norm,boundaryRePowerRow77_7Degree10Chunk12Norm,boundaryRePowerRow77_7Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_8Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-43039903891/8503056 : ℝ)) ((22-8)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-51993159655921/918330048 : ℝ)) ((22-8)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-36816383964341737/1410554953728 : ℝ)) ((22-8)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((2698941304137620131/152339935002624 : ℝ)) ((22-8)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_8Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_8Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_8Degree10Chunk0 x=boundaryRePowerRow77_8Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_8Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-10091284279338785291/2437438960041984 : ℝ)) ((22-8)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((618740256739823012981/1579460446107205632 : ℝ)) ((22-8)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((4356046131743194851953/113721152119718805504 : ℝ)) ((22-8)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-28321057871217096711049/2046980738154938499072 : ℝ)) ((22-8)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_8Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_8Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_8Degree10Chunk4 x=boundaryRePowerRow77_8Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_8Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((3326170804881961551697/2302853330424305811456 : ℝ)) ((22-8)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-128581347659693864508937/1768591357765866863198208 : ℝ)) ((22-8)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((162785130924697058101727/95503933319356810612703232 : ℝ)) ((22-8)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-6817004761674135994351/859535399874211295514329088 : ℝ)) ((22-8)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_8Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_8Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_8Degree10Chunk8 x=boundaryRePowerRow77_8Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_8Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-118830036176441743817/1289303099811316943271493632 : ℝ)) ((22-8)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-13668063861280363745/2900931974575463122360860672 : ℝ)) ((22-8)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((27750595395922238315/626601306508300034429945905152 : ℝ)) ((22-8)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((-12744276152806037/208867102169433344809981968384 : ℝ)) ((22-8)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_8Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_8Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_8Degree10Chunk12 x=boundaryRePowerRow77_8Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_8Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((21961341297329/4229558818931025232402134859776 : ℝ)) ((22-8)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((14325530485/114198088111137681274857641213952 : ℝ)) ((22-8)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_8Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_8Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_8Degree10Chunk16 x=boundaryRePowerRow77_8Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_8Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_8 10 x=c} := by

  have he : boundaryRePowerRow77_8 10 x=(((boundaryRePowerRow77_8Degree10Chunk0 x) + (boundaryRePowerRow77_8Degree10Chunk4 x)) + ((boundaryRePowerRow77_8Degree10Chunk8 x) + ((boundaryRePowerRow77_8Degree10Chunk12 x) + (boundaryRePowerRow77_8Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_8,boundaryRePowerRow77_8Degree10Chunk0,boundaryRePowerRow77_8Degree10Chunk4,boundaryRePowerRow77_8Degree10Chunk8,boundaryRePowerRow77_8Degree10Chunk12,boundaryRePowerRow77_8Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_8Degree10Chunk0Norm x).property,(boundaryRePowerRow77_8Degree10Chunk4Norm x).property,(boundaryRePowerRow77_8Degree10Chunk8Norm x).property,(boundaryRePowerRow77_8Degree10Chunk12Norm x).property,(boundaryRePowerRow77_8Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_8Degree10Chunk0Norm,boundaryRePowerRow77_8Degree10Chunk4Norm,boundaryRePowerRow77_8Degree10Chunk8Norm,boundaryRePowerRow77_8Degree10Chunk12Norm,boundaryRePowerRow77_8Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_9Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-231964931983/1594323 : ℝ)) ((22-9)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-210557044735907/918330048 : ℝ)) ((22-9)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((248462674122865985/2115832430592 : ℝ)) ((22-9)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-3320502011641449089/152339935002624 : ℝ)) ((22-9)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_9Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_9Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_9Degree10Chunk0 x=boundaryRePowerRow77_9Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_9Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-11336060693792637367/10968475320188928 : ℝ)) ((22-9)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((2831905986445154163811/1579460446107205632 : ℝ)) ((22-9)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((-47687123763919179400543/113721152119718805504 : ℝ)) ((22-9)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((45224940920577500951155/1023490369077469249536 : ℝ)) ((22-9)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_9Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_9Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_9Degree10Chunk4 x=boundaryRePowerRow77_9Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_9Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-6551210243106906428767/3070471107232407748608 : ℝ)) ((22-9)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((6863276214059699449571/442147839441466715799552 : ℝ)) ((22-9)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((153860227282608727952087/47751966659678405306351616 : ℝ)) ((22-9)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-6028302026926271670019/35813974994758803979763712 : ℝ)) ((22-9)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_9Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_9Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_9Degree10Chunk8 x=boundaryRePowerRow77_9Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_9Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((632928382634042059765/161162887476414617908936704 : ℝ)) ((22-9)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-20596470781475235377/644651549905658471635746816 : ℝ)) ((22-9)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((14178643823426880329/313300653254150017214972952576 : ℝ)) ((22-9)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((111320396915907529/1409852939643675077467378286592 : ℝ)) ((22-9)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_9Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_9Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_9Degree10Chunk12 x=boundaryRePowerRow77_9Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_9Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-6342698417503/117487744970306256455614857216 : ℝ)) ((22-9)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((2426981221/57099044055568840637428820606976 : ℝ)) ((22-9)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_9Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_9Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_9Degree10Chunk16 x=boundaryRePowerRow77_9Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_9Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_9 10 x=c} := by

  have he : boundaryRePowerRow77_9 10 x=(((boundaryRePowerRow77_9Degree10Chunk0 x) + (boundaryRePowerRow77_9Degree10Chunk4 x)) + ((boundaryRePowerRow77_9Degree10Chunk8 x) + ((boundaryRePowerRow77_9Degree10Chunk12 x) + (boundaryRePowerRow77_9Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_9,boundaryRePowerRow77_9Degree10Chunk0,boundaryRePowerRow77_9Degree10Chunk4,boundaryRePowerRow77_9Degree10Chunk8,boundaryRePowerRow77_9Degree10Chunk12,boundaryRePowerRow77_9Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_9Degree10Chunk0Norm x).property,(boundaryRePowerRow77_9Degree10Chunk4Norm x).property,(boundaryRePowerRow77_9Degree10Chunk8Norm x).property,(boundaryRePowerRow77_9Degree10Chunk12Norm x).property,(boundaryRePowerRow77_9Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_9Degree10Chunk0Norm,boundaryRePowerRow77_9Degree10Chunk4Norm,boundaryRePowerRow77_9Degree10Chunk8Norm,boundaryRePowerRow77_9Degree10Chunk12Norm,boundaryRePowerRow77_9Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_10Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-2118054708323/3188646 : ℝ)) ((22-10)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((56480011677895/229582512 : ℝ)) ((22-10)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((134058055137985705/4231664861184 : ℝ)) ((22-10)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-17815765018373067625/304679870005248 : ℝ)) ((22-10)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_10Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_10Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_10Degree10Chunk0 x=boundaryRePowerRow77_10Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_10Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_10Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((657569270106038332769/21936950640377856 : ℝ)) ((22-10)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-2727909046342592746033/394865111526801408 : ℝ)) ((22-10)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((41665285645354960385633/56860576059859402752 : ℝ)) ((22-10)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-45193801069645288518005/2046980738154938499072 : ℝ)) ((22-10)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_10Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_10Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_10Degree10Chunk4 x=boundaryRePowerRow77_10Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_10Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_10Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-190647925918021881910891/73691306573577785966592 : ℝ)) ((22-10)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((265826180879443913349661/884295678882933431599104 : ℝ)) ((22-10)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((-9320943547576114567169/663221759162200073699328 : ℝ)) ((22-10)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((4549686955444780899643/11937991664919601326587904 : ℝ)) ((22-10)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_10Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_10Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_10Degree10Chunk8 x=boundaryRePowerRow77_10Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_10Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_10Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-4960483886744146624255/644651549905658471635746816 : ℝ)) ((22-10)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((33161798203314162799/362616496821932890295107584 : ℝ)) ((22-10)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((-9756635795994252575/26108387771179168101247746048 : ℝ)) ((22-10)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((27234902191212835/78325163313537504303743238144 : ℝ)) ((22-10)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_10Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_10Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_10Degree10Chunk12 x=boundaryRePowerRow77_10Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_10Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_10Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((1292771330375/1409852939643675077467378286592 : ℝ)) ((22-10)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((-26945503417/38066029370379227091619213737984 : ℝ)) ((22-10)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_10Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_10Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_10Degree10Chunk16 x=boundaryRePowerRow77_10Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_10Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_10Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_10 10 x=c} := by

  have he : boundaryRePowerRow77_10 10 x=(((boundaryRePowerRow77_10Degree10Chunk0 x) + (boundaryRePowerRow77_10Degree10Chunk4 x)) + ((boundaryRePowerRow77_10Degree10Chunk8 x) + ((boundaryRePowerRow77_10Degree10Chunk12 x) + (boundaryRePowerRow77_10Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_10,boundaryRePowerRow77_10Degree10Chunk0,boundaryRePowerRow77_10Degree10Chunk4,boundaryRePowerRow77_10Degree10Chunk8,boundaryRePowerRow77_10Degree10Chunk12,boundaryRePowerRow77_10Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_10Degree10Chunk0Norm x).property,(boundaryRePowerRow77_10Degree10Chunk4Norm x).property,(boundaryRePowerRow77_10Degree10Chunk8Norm x).property,(boundaryRePowerRow77_10Degree10Chunk12Norm x).property,(boundaryRePowerRow77_10Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_10Degree10Chunk0Norm,boundaryRePowerRow77_10Degree10Chunk4Norm,boundaryRePowerRow77_10Degree10Chunk8Norm,boundaryRePowerRow77_10Degree10Chunk12Norm,boundaryRePowerRow77_10Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_11Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-360033540581/1594323 : ℝ)) ((22-11)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((17568454872499/28697814 : ℝ)) ((22-11)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-920524941361915531/2115832430592 : ℝ)) ((22-11)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((73496748484323052529/304679870005248 : ℝ)) ((22-11)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_11Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_11Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_11Degree10Chunk0 x=boundaryRePowerRow77_11Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_11Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-27429392756818027649/457019805007872 : ℝ)) ((22-11)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((3978806380121646237391/789730223053602816 : ℝ)) ((22-11)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((13225175638740216702139/28430288029929701376 : ℝ)) ((22-11)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-4046844871148757577/29249267520503808 : ℝ)) ((22-11)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_11Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_11Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_11Degree10Chunk4 x=boundaryRePowerRow77_11Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_11Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((477167294277387620196913/36845653286788892983296 : ℝ)) ((22-11)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-206070765128072537541793/331610879581100036849664 : ℝ)) ((22-11)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((178347676301480892829787/11937991664919601326587904 : ℝ)) ((22-11)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-1365558175881921806213/11937991664919601326587904 : ℝ)) ((22-11)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_11Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_11Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_11Degree10Chunk8 x=boundaryRePowerRow77_11Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_11Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((636471752928721651/35813974994758803979763712 : ℝ)) ((22-11)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-21188485667851309369/483488662429243853726810112 : ℝ)) ((22-11)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((12462386243290758229/26108387771179168101247746048 : ℝ)) ((22-11)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((-78105652709244055/78325163313537504303743238144 : ℝ)) ((22-11)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_11Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_11Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_11Degree10Chunk12 x=boundaryRePowerRow77_11Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_11Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((26240936749825/78325163313537504303743238144 : ℝ)) ((22-11)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((7534594907/1057389704732756308100533714944 : ℝ)) ((22-11)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_11Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_11Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_11Degree10Chunk16 x=boundaryRePowerRow77_11Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_11Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_11 10 x=c} := by

  have he : boundaryRePowerRow77_11 10 x=(((boundaryRePowerRow77_11Degree10Chunk0 x) + (boundaryRePowerRow77_11Degree10Chunk4 x)) + ((boundaryRePowerRow77_11Degree10Chunk8 x) + ((boundaryRePowerRow77_11Degree10Chunk12 x) + (boundaryRePowerRow77_11Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_11,boundaryRePowerRow77_11Degree10Chunk0,boundaryRePowerRow77_11Degree10Chunk4,boundaryRePowerRow77_11Degree10Chunk8,boundaryRePowerRow77_11Degree10Chunk12,boundaryRePowerRow77_11Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_11Degree10Chunk0Norm x).property,(boundaryRePowerRow77_11Degree10Chunk4Norm x).property,(boundaryRePowerRow77_11Degree10Chunk8Norm x).property,(boundaryRePowerRow77_11Degree10Chunk12Norm x).property,(boundaryRePowerRow77_11Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_11Degree10Chunk0Norm,boundaryRePowerRow77_11Degree10Chunk4Norm,boundaryRePowerRow77_11Degree10Chunk8Norm,boundaryRePowerRow77_11Degree10Chunk12Norm,boundaryRePowerRow77_11Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_12Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((2115896746330/1594323 : ℝ)) ((22-12)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-4887845985995/4782969 : ℝ)) ((22-12)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((452481369635861897/470184984576 : ℝ)) ((22-12)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-735812267157759707/3173748645888 : ℝ)) ((22-12)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_12Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_12Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_12Degree10Chunk0 x=boundaryRePowerRow77_12Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_12Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-75435289208493100207/3656158440062976 : ℝ)) ((22-12)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((888373109037337581125/49358138940850176 : ℝ)) ((22-12)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((-191721690042457850287/55527906308456448 : ℝ)) ((22-12)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((1613838269297808138013/4738381338321616896 : ℝ)) ((22-12)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_12Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_12Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_12Degree10Chunk4 x=boundaryRePowerRow77_12Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_12Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-172121852342837169901975/9211413321697223245824 : ℝ)) ((22-12)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((37425770717325900097697/82902719895275009212416 : ℝ)) ((22-12)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((38681680767025580551/4605706660848611622912 : ℝ)) ((22-12)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-48847947315614820159353/53720962492138205969645568 : ℝ)) ((22-12)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_12Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_12Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_12Degree10Chunk8 x=boundaryRePowerRow77_12Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_12Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((5853187574794241724079/241744331214621926863405056 : ℝ)) ((22-12)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-52898768435336212561/241744331214621926863405056 : ℝ)) ((22-12)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((383697734414416087/815887117849349003163992064 : ℝ)) ((22-12)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((1236361820156059/4351397961863194683541291008 : ℝ)) ((22-12)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_12Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_12Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_12Degree10Chunk12 x=boundaryRePowerRow77_12Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_12Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-3132177223889/6527096942794792025311936512 : ℝ)) ((22-12)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((-758012507/132173713091594538512566714368 : ℝ)) ((22-12)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_12Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_12Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_12Degree10Chunk16 x=boundaryRePowerRow77_12Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_12Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_12 10 x=c} := by

  have he : boundaryRePowerRow77_12 10 x=(((boundaryRePowerRow77_12Degree10Chunk0 x) + (boundaryRePowerRow77_12Degree10Chunk4 x)) + ((boundaryRePowerRow77_12Degree10Chunk8 x) + ((boundaryRePowerRow77_12Degree10Chunk12 x) + (boundaryRePowerRow77_12Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_12,boundaryRePowerRow77_12Degree10Chunk0,boundaryRePowerRow77_12Degree10Chunk4,boundaryRePowerRow77_12Degree10Chunk8,boundaryRePowerRow77_12Degree10Chunk12,boundaryRePowerRow77_12Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_12Degree10Chunk0Norm x).property,(boundaryRePowerRow77_12Degree10Chunk4Norm x).property,(boundaryRePowerRow77_12Degree10Chunk8Norm x).property,(boundaryRePowerRow77_12Degree10Chunk12Norm x).property,(boundaryRePowerRow77_12Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_12Degree10Chunk0Norm,boundaryRePowerRow77_12Degree10Chunk4Norm,boundaryRePowerRow77_12Degree10Chunk8Norm,boundaryRePowerRow77_12Degree10Chunk12Norm,boundaryRePowerRow77_12Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_13Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((114719017340/531441 : ℝ)) ((22-13)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((3221264502340/1594323 : ℝ)) ((22-13)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-33439209471454373/2115832430592 : ℝ)) ((22-13)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-21222272779248714413/38084983750656 : ℝ)) ((22-13)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_13Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_13Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_13Degree10Chunk0 x=boundaryRePowerRow77_13Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_13Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_13Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((105788716395505184105/457019805007872 : ℝ)) ((22-13)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-4527507267961596325865/98716277881700352 : ℝ)) ((22-13)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((37874640804033095876825/7107572007482425344 : ℝ)) ((22-13)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-1492942879875765628315/3998009254208864256 : ℝ)) ((22-13)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_13Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_13Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_13Degree10Chunk4 x=boundaryRePowerRow77_13Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_13Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_13Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((115933709965584087279551/9211413321697223245824 : ℝ)) ((22-13)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((24866062742864992766795/82902719895275009212416 : ℝ)) ((22-13)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((-40445270447041873837189/746124479057475082911744 : ℝ)) ((22-13)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((930892117094983328173/373062239528737541455872 : ℝ)) ((22-13)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_13Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_13Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_13Degree10Chunk8 x=boundaryRePowerRow77_13Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_13Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_13Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-13564531176772919328887/241744331214621926863405056 : ℝ)) ((22-13)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((1276070651702658008447/2175698980931597341770645504 : ℝ)) ((22-13)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((-2496526281237265085/1087849490465798670885322752 : ℝ)) ((22-13)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((2787216140415433/1087849490465798670885322752 : ℝ)) ((22-13)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_13Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_13Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_13Degree10Chunk12 x=boundaryRePowerRow77_13Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_13Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_13Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-2022407420621/6527096942794792025311936512 : ℝ)) ((22-13)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((-11700680453/176231617455459384683422285824 : ℝ)) ((22-13)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_13Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_13Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_13Degree10Chunk16 x=boundaryRePowerRow77_13Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_13Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_13Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_13 10 x=c} := by

  have he : boundaryRePowerRow77_13 10 x=(((boundaryRePowerRow77_13Degree10Chunk0 x) + (boundaryRePowerRow77_13Degree10Chunk4 x)) + ((boundaryRePowerRow77_13Degree10Chunk8 x) + ((boundaryRePowerRow77_13Degree10Chunk12 x) + (boundaryRePowerRow77_13Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_13,boundaryRePowerRow77_13Degree10Chunk0,boundaryRePowerRow77_13Degree10Chunk4,boundaryRePowerRow77_13Degree10Chunk8,boundaryRePowerRow77_13Degree10Chunk12,boundaryRePowerRow77_13Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_13Degree10Chunk0Norm x).property,(boundaryRePowerRow77_13Degree10Chunk4Norm x).property,(boundaryRePowerRow77_13Degree10Chunk8Norm x).property,(boundaryRePowerRow77_13Degree10Chunk12Norm x).property,(boundaryRePowerRow77_13Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_13Degree10Chunk0Norm,boundaryRePowerRow77_13Degree10Chunk4Norm,boundaryRePowerRow77_13Degree10Chunk8Norm,boundaryRePowerRow77_13Degree10Chunk12Norm,boundaryRePowerRow77_13Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_14Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((5394966086360/1594323 : ℝ)) ((22-14)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((39350588681348/14348907 : ℝ)) ((22-14)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-3589142796807723451/1057916215296 : ℝ)) ((22-14)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((3321917108806349755/2380311484416 : ℝ)) ((22-14)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_14Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_14Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_14Degree10Chunk0 x=boundaryRePowerRow77_14Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_14Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-217657400230905663265/685529707511808 : ℝ)) ((22-14)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((1100265958586151215/24100653779712 : ℝ)) ((22-14)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((-15237509241550300368319/3553786003741212672 : ℝ)) ((22-14)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((14274429312099492278899/63968148067341828096 : ℝ)) ((22-14)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_14Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_14Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_14Degree10Chunk4 x=boundaryRePowerRow77_14Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_14Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((13675116414641514484481/4605706660848611622912 : ℝ)) ((22-14)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-42489802366065464004667/27634239965091669737472 : ℝ)) ((22-14)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((29166773656570587434287/248708159685825027637248 : ℝ)) ((22-14)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-7157306975615495392435/1678780077879318936551424 : ℝ)) ((22-14)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_14Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_14Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_14Degree10Chunk8 x=boundaryRePowerRow77_14Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_14Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((50873455678515303779/629542529204744601206784 : ℝ)) ((22-14)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-755264063166663593/944313793807116901810176 : ℝ)) ((22-14)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((70721978665527299/20145360934551827238617088 : ℝ)) ((22-14)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((-160769608743479/30218041401827740857925632 : ℝ)) ((22-14)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_14Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_14Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_14Degree10Chunk12 x=boundaryRePowerRow77_14Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_14Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((25561885391/15109020700913870428962816 : ℝ)) ((22-14)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((72277303/543924745232899335442661376 : ℝ)) ((22-14)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_14Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_14Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_14Degree10Chunk16 x=boundaryRePowerRow77_14Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_14Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_14 10 x=c} := by

  have he : boundaryRePowerRow77_14 10 x=(((boundaryRePowerRow77_14Degree10Chunk0 x) + (boundaryRePowerRow77_14Degree10Chunk4 x)) + ((boundaryRePowerRow77_14Degree10Chunk8 x) + ((boundaryRePowerRow77_14Degree10Chunk12 x) + (boundaryRePowerRow77_14Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_14,boundaryRePowerRow77_14Degree10Chunk0,boundaryRePowerRow77_14Degree10Chunk4,boundaryRePowerRow77_14Degree10Chunk8,boundaryRePowerRow77_14Degree10Chunk12,boundaryRePowerRow77_14Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_14Degree10Chunk0Norm x).property,(boundaryRePowerRow77_14Degree10Chunk4Norm x).property,(boundaryRePowerRow77_14Degree10Chunk8Norm x).property,(boundaryRePowerRow77_14Degree10Chunk12Norm x).property,(boundaryRePowerRow77_14Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_14Degree10Chunk0Norm,boundaryRePowerRow77_14Degree10Chunk4Norm,boundaryRePowerRow77_14Degree10Chunk8Norm,boundaryRePowerRow77_14Degree10Chunk12Norm,boundaryRePowerRow77_14Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_15Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((13563919004608/1594323 : ℝ)) ((22-15)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((-37984810940960/4782969 : ℝ)) ((22-15)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((1955412045322578445/528958107648 : ℝ)) ((22-15)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-835620800934279901/793437161472 : ℝ)) ((22-15)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_15Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_15Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_15Degree10Chunk0 x=boundaryRePowerRow77_15Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_15Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((22691434948548053101/114254951251968 : ℝ)) ((22-15)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((-52590016560273871169/2056589122535424 : ℝ)) ((22-15)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((128301344524369850393/65810851921133568 : ℝ)) ((22-15)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((145160439264704640047/10661358011223638016 : ℝ)) ((22-15)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_15Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_15Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_15Degree10Chunk4 x=boundaryRePowerRow77_15Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_15Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-3072446940346684817225/127936296134683656192 : ℝ)) ((22-15)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((119666949353033694298499/41451359947637504606208 : ℝ)) ((22-15)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((-21031234662045789362075/124354079842912513818624 : ℝ)) ((22-15)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((17522417463260795714321/3357560155758637873102848 : ℝ)) ((22-15)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_15Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_15Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_15Degree10Chunk8 x=boundaryRePowerRow77_15Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_15Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-69652784203948633385/839390038939659468275712 : ℝ)) ((22-15)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((7099975357912210705/10072680467275913619308544 : ℝ)) ((22-15)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((-30795092088100715/10072680467275913619308544 : ℝ)) ((22-15)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((54348775355899/10072680467275913619308544 : ℝ)) ((22-15)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_15Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_15Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_15Degree10Chunk12 x=boundaryRePowerRow77_15Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_15Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-13358326883/5036340233637956809654272 : ℝ)) ((22-15)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((18989215/203971779462337250790998016 : ℝ)) ((22-15)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_15Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_15Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_15Degree10Chunk16 x=boundaryRePowerRow77_15Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_15Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_15 10 x=c} := by

  have he : boundaryRePowerRow77_15 10 x=(((boundaryRePowerRow77_15Degree10Chunk0 x) + (boundaryRePowerRow77_15Degree10Chunk4 x)) + ((boundaryRePowerRow77_15Degree10Chunk8 x) + ((boundaryRePowerRow77_15Degree10Chunk12 x) + (boundaryRePowerRow77_15Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_15,boundaryRePowerRow77_15Degree10Chunk0,boundaryRePowerRow77_15Degree10Chunk4,boundaryRePowerRow77_15Degree10Chunk8,boundaryRePowerRow77_15Degree10Chunk12,boundaryRePowerRow77_15Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_15Degree10Chunk0Norm x).property,(boundaryRePowerRow77_15Degree10Chunk4Norm x).property,(boundaryRePowerRow77_15Degree10Chunk8Norm x).property,(boundaryRePowerRow77_15Degree10Chunk12Norm x).property,(boundaryRePowerRow77_15Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_15Degree10Chunk0Norm,boundaryRePowerRow77_15Degree10Chunk4Norm,boundaryRePowerRow77_15Degree10Chunk8Norm,boundaryRePowerRow77_15Degree10Chunk12Norm,boundaryRePowerRow77_15Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_16Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-2280513882496/1594323 : ℝ)) ((22-16)+2*0-6) 0 0 10 x) + (boundaryTermPowerRow77 ((38642214431872/14348907 : ℝ)) ((22-16)+2*1-6) 0 1 10 x)) + ((boundaryTermPowerRow77 ((-5027075167090235/3265173504 : ℝ)) ((22-16)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((115014345418774361/264479053824 : ℝ)) ((22-16)+2*3-6) 0 3 10 x)))

def boundaryRePowerRow77_16Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_16Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_16Degree10Chunk0 x=boundaryRePowerRow77_16Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_16Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_16Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-8228038022974059391/114254951251968 : ℝ)) ((22-16)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((3164816948286127745/514147280633856 : ℝ)) ((22-16)+2*5-6) 0 5 10 x)) + ((boundaryTermPowerRow77 ((118335823536562382989/296148833645101056 : ℝ)) ((22-16)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((-204118511716521456295/888446500935303168 : ℝ)) ((22-16)+2*7-6) 0 7 10 x)))

def boundaryRePowerRow77_16Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_16Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_16Degree10Chunk4 x=boundaryRePowerRow77_16Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_16Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_16Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((14217058126033528159781/383808888404050968576 : ℝ)) ((22-16)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((-67296295829398153290253/20725679973818752303104 : ℝ)) ((22-16)+2*9-6) 0 9 10 x)) + ((boundaryTermPowerRow77 ((60664994436785965393673/373062239528737541455872 : ℝ)) ((22-16)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((-4958718258837756564619/1119186718586212624367616 : ℝ)) ((22-16)+2*11-6) 0 11 10 x)))

def boundaryRePowerRow77_16Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_16Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_16Degree10Chunk8 x=boundaryRePowerRow77_16Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_16Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_16Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((16690238053394868131/279796679646553156091904 : ℝ)) ((22-16)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-18624987334963153/46632779941092192681984 : ℝ)) ((22-16)+2*13-6) 0 13 10 x)) + ((boundaryTermPowerRow77 ((5106683045381761/3357560155758637873102848 : ℝ)) ((22-16)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((-10575635694101/3357560155758637873102848 : ℝ)) ((22-16)+2*15-6) 0 15 10 x)))

def boundaryRePowerRow77_16Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_16Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_16Degree10Chunk12 x=boundaryRePowerRow77_16Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_16Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_16Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((13269937105/5036340233637956809654272 : ℝ)) ((22-16)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((-4489513/8498824144264052116291584 : ℝ)) ((22-16)+2*17-6) 0 17 10 x))

def boundaryRePowerRow77_16Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_16Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_16Degree10Chunk16 x=boundaryRePowerRow77_16Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_16Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_16Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_16 10 x=c} := by

  have he : boundaryRePowerRow77_16 10 x=(((boundaryRePowerRow77_16Degree10Chunk0 x) + (boundaryRePowerRow77_16Degree10Chunk4 x)) + ((boundaryRePowerRow77_16Degree10Chunk8 x) + ((boundaryRePowerRow77_16Degree10Chunk12 x) + (boundaryRePowerRow77_16Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_16,boundaryRePowerRow77_16Degree10Chunk0,boundaryRePowerRow77_16Degree10Chunk4,boundaryRePowerRow77_16Degree10Chunk8,boundaryRePowerRow77_16Degree10Chunk12,boundaryRePowerRow77_16Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_16Degree10Chunk0Norm x).property,(boundaryRePowerRow77_16Degree10Chunk4Norm x).property,(boundaryRePowerRow77_16Degree10Chunk8Norm x).property,(boundaryRePowerRow77_16Degree10Chunk12Norm x).property,(boundaryRePowerRow77_16Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_16Degree10Chunk0Norm,boundaryRePowerRow77_16Degree10Chunk4Norm,boundaryRePowerRow77_16Degree10Chunk8Norm,boundaryRePowerRow77_16Degree10Chunk12Norm,boundaryRePowerRow77_16Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_17Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-1199292895232/531441 : ℝ)) ((22-17)+2*1-6) 0 1 10 x) + (boundaryTermPowerRow77 ((8944684236155561/14693280768 : ℝ)) ((22-17)+2*2-6) 0 2 10 x)) + ((boundaryTermPowerRow77 ((-8683150037025379/264479053824 : ℝ)) ((22-17)+2*3-6) 0 3 10 x) + (boundaryTermPowerRow77 ((-187436597613540635/9521245937664 : ℝ)) ((22-17)+2*4-6) 0 4 10 x)))

def boundaryRePowerRow77_17Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_17Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_17Degree10Chunk0 x=boundaryRePowerRow77_17Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_17Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((2375754080265139879/342764853755904 : ℝ)) ((22-17)+2*5-6) 0 5 10 x) + (boundaryTermPowerRow77 ((-12481067345496906211/8226356490141696 : ℝ)) ((22-17)+2*6-6) 0 6 10 x)) + ((boundaryTermPowerRow77 ((112471540232634081337/444223250467651584 : ℝ)) ((22-17)+2*7-6) 0 7 10 x) + (boundaryTermPowerRow77 ((-1903538488994906298383/63968148067341828096 : ℝ)) ((22-17)+2*8-6) 0 8 10 x)))

def boundaryRePowerRow77_17Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_17Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_17Degree10Chunk4 x=boundaryRePowerRow77_17Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_17Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((975245758317349834675/431784999454557339648 : ℝ)) ((22-17)+2*9-6) 0 9 10 x) + (boundaryTermPowerRow77 ((-2131079243627675191859/20725679973818752303104 : ℝ)) ((22-17)+2*10-6) 0 10 10 x)) + ((boundaryTermPowerRow77 ((2456531140649170829/971516248772754014208 : ℝ)) ((22-17)+2*11-6) 0 11 10 x) + (boundaryTermPowerRow77 ((-323330429893532167/11658194985273048170496 : ℝ)) ((22-17)+2*12-6) 0 12 10 x)))

def boundaryRePowerRow77_17Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_17Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_17Degree10Chunk8 x=boundaryRePowerRow77_17Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_17Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((3650124895641203/34974584955819144511488 : ℝ)) ((22-17)+2*13-6) 0 13 10 x) + (boundaryTermPowerRow77 ((-872295575383/6908559991272917434368 : ℝ)) ((22-17)+2*14-6) 0 14 10 x)) + ((boundaryTermPowerRow77 ((155131275655/279796679646553156091904 : ℝ)) ((22-17)+2*15-6) 0 15 10 x) + (boundaryTermPowerRow77 ((-604640819/419695019469829734137856 : ℝ)) ((22-17)+2*16-6) 0 16 10 x)))

def boundaryRePowerRow77_17Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_17Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_17Degree10Chunk12 x=boundaryRePowerRow77_17Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_17Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 ((13254793/22663531051370805643444224 : ℝ)) ((22-17)+2*17-6) 0 17 10 x)

def boundaryRePowerRow77_17Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_17Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_17Degree10Chunk16 x=boundaryRePowerRow77_17Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_17Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_17 10 x=c} := by

  have he : boundaryRePowerRow77_17 10 x=(((boundaryRePowerRow77_17Degree10Chunk0 x) + (boundaryRePowerRow77_17Degree10Chunk4 x)) + ((boundaryRePowerRow77_17Degree10Chunk8 x) + ((boundaryRePowerRow77_17Degree10Chunk12 x) + (boundaryRePowerRow77_17Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_17,boundaryRePowerRow77_17Degree10Chunk0,boundaryRePowerRow77_17Degree10Chunk4,boundaryRePowerRow77_17Degree10Chunk8,boundaryRePowerRow77_17Degree10Chunk12,boundaryRePowerRow77_17Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_17Degree10Chunk0Norm x).property,(boundaryRePowerRow77_17Degree10Chunk4Norm x).property,(boundaryRePowerRow77_17Degree10Chunk8Norm x).property,(boundaryRePowerRow77_17Degree10Chunk12Norm x).property,(boundaryRePowerRow77_17Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_17Degree10Chunk0Norm,boundaryRePowerRow77_17Degree10Chunk4Norm,boundaryRePowerRow77_17Degree10Chunk8Norm,boundaryRePowerRow77_17Degree10Chunk12Norm,boundaryRePowerRow77_17Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_18Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-375750311936/531441 : ℝ)) ((22-18)+2*1-6) 0 1 10 x) + (boundaryTermPowerRow77 ((421183371165691/816293376 : ℝ)) ((22-18)+2*2-6) 0 2 10 x)) + ((boundaryTermPowerRow77 ((-8457817153131913/44079842304 : ℝ)) ((22-18)+2*3-6) 0 3 10 x) + (boundaryTermPowerRow77 ((133891807211385611/3173748645888 : ℝ)) ((22-18)+2*4-6) 0 4 10 x)))

def boundaryRePowerRow77_18Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_18Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_18Degree10Chunk0 x=boundaryRePowerRow77_18Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_18Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-370690693657613579/57127475625984 : ℝ)) ((22-18)+2*5-6) 0 5 10 x) + (boundaryTermPowerRow77 ((407819072049208669/457019805007872 : ℝ)) ((22-18)+2*6-6) 0 6 10 x)) + ((boundaryTermPowerRow77 ((-35745420741850372343/296148833645101056 : ℝ)) ((22-18)+2*7-6) 0 7 10 x) + (boundaryTermPowerRow77 ((70229091406890953501/5330679005611819008 : ℝ)) ((22-18)+2*8-6) 0 8 10 x)))

def boundaryRePowerRow77_18Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_18Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_18Degree10Chunk4 x=boundaryRePowerRow77_18Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_18Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-1098982786589008091093/1151426665212152905728 : ℝ)) ((22-18)+2*9-6) 0 9 10 x) + (boundaryTermPowerRow77 ((23374696935716413813/575713332606076452864 : ℝ)) ((22-18)+2*10-6) 0 10 10 x)) + ((boundaryTermPowerRow77 ((-13337893701029924839/15544259980364064227328 : ℝ)) ((22-18)+2*11-6) 0 11 10 x) + (boundaryTermPowerRow77 ((152839347767787587/31088519960728128454656 : ℝ)) ((22-18)+2*12-6) 0 12 10 x)))

def boundaryRePowerRow77_18Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_18Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_18Degree10Chunk8 x=boundaryRePowerRow77_18Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_18Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((165153809425039/2914548746318262042624 : ℝ)) ((22-18)+2*13-6) 0 13 10 x) + (boundaryTermPowerRow77 ((-6559141010815/11658194985273048170496 : ℝ)) ((22-18)+2*14-6) 0 14 10 x)) + ((boundaryTermPowerRow77 ((161914001255/139898339823276578045952 : ℝ)) ((22-18)+2*15-6) 0 15 10 x) + (boundaryTermPowerRow77 ((-31648931/93265559882184385363968 : ℝ)) ((22-18)+2*16-6) 0 16 10 x)))

def boundaryRePowerRow77_18Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_18Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_18Degree10Chunk12 x=boundaryRePowerRow77_18Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_18Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 ((-3202801/22663531051370805643444224 : ℝ)) ((22-18)+2*17-6) 0 17 10 x)

def boundaryRePowerRow77_18Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_18Degree10Chunk16 x=c} := by

  have he : boundaryRePowerRow77_18Degree10Chunk16 x=boundaryRePowerRow77_18Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_18Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_18 10 x=c} := by

  have he : boundaryRePowerRow77_18 10 x=(((boundaryRePowerRow77_18Degree10Chunk0 x) + (boundaryRePowerRow77_18Degree10Chunk4 x)) + ((boundaryRePowerRow77_18Degree10Chunk8 x) + ((boundaryRePowerRow77_18Degree10Chunk12 x) + (boundaryRePowerRow77_18Degree10Chunk16 x)))) := by

    dsimp only [boundaryRePowerRow77_18,boundaryRePowerRow77_18Degree10Chunk0,boundaryRePowerRow77_18Degree10Chunk4,boundaryRePowerRow77_18Degree10Chunk8,boundaryRePowerRow77_18Degree10Chunk12,boundaryRePowerRow77_18Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_18Degree10Chunk0Norm x).property,(boundaryRePowerRow77_18Degree10Chunk4Norm x).property,(boundaryRePowerRow77_18Degree10Chunk8Norm x).property,(boundaryRePowerRow77_18Degree10Chunk12Norm x).property,(boundaryRePowerRow77_18Degree10Chunk16Norm x).property]

    dsimp only [boundaryRePowerRow77_18Degree10Chunk0Norm,boundaryRePowerRow77_18Degree10Chunk4Norm,boundaryRePowerRow77_18Degree10Chunk8Norm,boundaryRePowerRow77_18Degree10Chunk12Norm,boundaryRePowerRow77_18Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_19Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-89727402628717/408146688 : ℝ)) ((22-19)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((1048897307666959/14693280768 : ℝ)) ((22-19)+2*3-6) 0 3 10 x)) + ((boundaryTermPowerRow77 ((-3295831149082177/264479053824 : ℝ)) ((22-19)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((16116813321962179/12694994583552 : ℝ)) ((22-19)+2*5-6) 0 5 10 x)))

def boundaryRePowerRow77_19Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_19Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_19Degree10Chunk0 x=boundaryRePowerRow77_19Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_19Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_19Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-77928912523889347/685529707511808 : ℝ)) ((22-19)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((204117221675779999/12339534735212544 : ℝ)) ((22-19)+2*7-6) 0 7 10 x)) + ((boundaryTermPowerRow77 ((-52291721529779/24100653779712 : ℝ)) ((22-19)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((3847406362216530181/23988055525253185536 : ℝ)) ((22-19)+2*9-6) 0 9 10 x)))

def boundaryRePowerRow77_19Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_19Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_19Degree10Chunk4 x=boundaryRePowerRow77_19Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_19Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_19Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-9326284373807451169/1727139997818229358592 : ℝ)) ((22-19)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((24568017717062699/5181419993454688075776 : ℝ)) ((22-19)+2*11-6) 0 11 10 x)) + ((boundaryTermPowerRow77 ((22640030757368255/5181419993454688075776 : ℝ)) ((22-19)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((-710386886024143/7772129990182032113664 : ℝ)) ((22-19)+2*13-6) 0 13 10 x)))

def boundaryRePowerRow77_19Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_19Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_19Degree10Chunk8 x=boundaryRePowerRow77_19Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_19Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_19Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((9758298288875/15544259980364064227328 : ℝ)) ((22-19)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((-8144037407/5181419993454688075776 : ℝ)) ((22-19)+2*15-6) 0 15 10 x)) + ((boundaryTermPowerRow77 ((180714913/139898339823276578045952 : ℝ)) ((22-19)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((-434041/1888627587614233803620352 : ℝ)) ((22-19)+2*17-6) 0 17 10 x)))

def boundaryRePowerRow77_19Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_19Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_19Degree10Chunk12 x=boundaryRePowerRow77_19Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_19Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_19Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_19 10 x=c} := by

  have he : boundaryRePowerRow77_19 10 x=(((boundaryRePowerRow77_19Degree10Chunk0 x) + (boundaryRePowerRow77_19Degree10Chunk4 x)) + ((boundaryRePowerRow77_19Degree10Chunk8 x) + (boundaryRePowerRow77_19Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_19,boundaryRePowerRow77_19Degree10Chunk0,boundaryRePowerRow77_19Degree10Chunk4,boundaryRePowerRow77_19Degree10Chunk8,boundaryRePowerRow77_19Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_19Degree10Chunk0Norm x).property,(boundaryRePowerRow77_19Degree10Chunk4Norm x).property,(boundaryRePowerRow77_19Degree10Chunk8Norm x).property,(boundaryRePowerRow77_19Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_19Degree10Chunk0Norm,boundaryRePowerRow77_19Degree10Chunk4Norm,boundaryRePowerRow77_19Degree10Chunk8Norm,boundaryRePowerRow77_19Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_20Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((3556367801657/34012224 : ℝ)) ((22-20)+2*2-6) 0 2 10 x) + (boundaryTermPowerRow77 ((-14723747455213/612220032 : ℝ)) ((22-20)+2*3-6) 0 3 10 x)) + ((boundaryTermPowerRow77 ((319944259319861/176319369216 : ℝ)) ((22-20)+2*4-6) 0 4 10 x) + (boundaryTermPowerRow77 ((603041593462733/1586874322944 : ℝ)) ((22-20)+2*5-6) 0 5 10 x)))

def boundaryRePowerRow77_20Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_20Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_20Degree10Chunk0 x=boundaryRePowerRow77_20Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_20Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-1024458717848417/8463329722368 : ℝ)) ((22-20)+2*6-6) 0 6 10 x) + (boundaryTermPowerRow77 ((33439102748176391/2056589122535424 : ℝ)) ((22-20)+2*7-6) 0 7 10 x)) + ((boundaryTermPowerRow77 ((-412963346704651303/296148833645101056 : ℝ)) ((22-20)+2*8-6) 0 8 10 x) + (boundaryTermPowerRow77 ((356624431433807509/3998009254208864256 : ℝ)) ((22-20)+2*9-6) 0 9 10 x)))

def boundaryRePowerRow77_20Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_20Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_20Degree10Chunk4 x=boundaryRePowerRow77_20Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_20Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-13692029644271483/2998506940656648192 : ℝ)) ((22-20)+2*10-6) 0 10 10 x) + (boundaryTermPowerRow77 ((16911220892262683/95952222101012742144 : ℝ)) ((22-20)+2*11-6) 0 11 10 x)) + ((boundaryTermPowerRow77 ((-948973981549615/215892499727278669824 : ℝ)) ((22-20)+2*12-6) 0 12 10 x) + (boundaryTermPowerRow77 ((76506878907493/1295354998363672018944 : ℝ)) ((22-20)+2*13-6) 0 13 10 x)))

def boundaryRePowerRow77_20Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_20Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_20Degree10Chunk8 x=boundaryRePowerRow77_20Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_20Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-241881063457/647677499181836009472 : ℝ)) ((22-20)+2*14-6) 0 14 10 x) + (boundaryTermPowerRow77 ((7830818323/7772129990182032113664 : ℝ)) ((22-20)+2*15-6) 0 15 10 x)) + ((boundaryTermPowerRow77 ((-1911013/1943032497545508028416 : ℝ)) ((22-20)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((11819/52461877433728716767232 : ℝ)) ((22-20)+2*17-6) 0 17 10 x)))

def boundaryRePowerRow77_20Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_20Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_20Degree10Chunk12 x=boundaryRePowerRow77_20Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_20Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_20 10 x=c} := by

  have he : boundaryRePowerRow77_20 10 x=(((boundaryRePowerRow77_20Degree10Chunk0 x) + (boundaryRePowerRow77_20Degree10Chunk4 x)) + ((boundaryRePowerRow77_20Degree10Chunk8 x) + (boundaryRePowerRow77_20Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_20,boundaryRePowerRow77_20Degree10Chunk0,boundaryRePowerRow77_20Degree10Chunk4,boundaryRePowerRow77_20Degree10Chunk8,boundaryRePowerRow77_20Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_20Degree10Chunk0Norm x).property,(boundaryRePowerRow77_20Degree10Chunk4Norm x).property,(boundaryRePowerRow77_20Degree10Chunk8Norm x).property,(boundaryRePowerRow77_20Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_20Degree10Chunk0Norm,boundaryRePowerRow77_20Degree10Chunk4Norm,boundaryRePowerRow77_20Degree10Chunk8Norm,boundaryRePowerRow77_20Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_21Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-52125568405/25509168 : ℝ)) ((22-21)+2*3-6) 0 3 10 x) + (boundaryTermPowerRow77 ((3541517122583/1836660096 : ℝ)) ((22-21)+2*4-6) 0 4 10 x)) + ((boundaryTermPowerRow77 ((-38816024418325/66119763456 : ℝ)) ((22-21)+2*5-6) 0 5 10 x) + (boundaryTermPowerRow77 ((55848590646085/528958107648 : ℝ)) ((22-21)+2*6-6) 0 6 10 x)))

def boundaryRePowerRow77_21Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_21Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_21Degree10Chunk0 x=boundaryRePowerRow77_21Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_21Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-544701864665579/42845606719488 : ℝ)) ((22-21)+2*7-6) 0 7 10 x) + (boundaryTermPowerRow77 ((1662459929233771/1542441841901568 : ℝ)) ((22-21)+2*8-6) 0 8 10 x)) + ((boundaryTermPowerRow77 ((-10942077893885723/166583718925369344 : ℝ)) ((22-21)+2*9-6) 0 9 10 x) + (boundaryTermPowerRow77 ((956688408399985/333167437850738688 : ℝ)) ((22-21)+2*10-6) 0 10 10 x)))

def boundaryRePowerRow77_21Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_21Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_21Degree10Chunk4 x=boundaryRePowerRow77_21Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_21Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-3146705839806479/35982083287879778304 : ℝ)) ((22-21)+2*11-6) 0 11 10 x) + (boundaryTermPowerRow77 ((250416060102239/143928333151519113216 : ℝ)) ((22-21)+2*12-6) 0 12 10 x)) + ((boundaryTermPowerRow77 ((-8780817403579/431784999454557339648 : ℝ)) ((22-21)+2*13-6) 0 13 10 x) + (boundaryTermPowerRow77 ((79807762975/647677499181836009472 : ℝ)) ((22-21)+2*14-6) 0 14 10 x)))

def boundaryRePowerRow77_21Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_21Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_21Degree10Chunk8 x=boundaryRePowerRow77_21Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_21Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-24357643/71964166575759556608 : ℝ)) ((22-21)+2*15-6) 0 15 10 x) + ((boundaryTermPowerRow77 ((446395/1295354998363672018944 : ℝ)) ((22-21)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((-8669/104923754867457433534464 : ℝ)) ((22-21)+2*17-6) 0 17 10 x)))

def boundaryRePowerRow77_21Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_21Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_21Degree10Chunk12 x=boundaryRePowerRow77_21Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_21Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_21 10 x=c} := by

  have he : boundaryRePowerRow77_21 10 x=(((boundaryRePowerRow77_21Degree10Chunk0 x) + (boundaryRePowerRow77_21Degree10Chunk4 x)) + ((boundaryRePowerRow77_21Degree10Chunk8 x) + (boundaryRePowerRow77_21Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_21,boundaryRePowerRow77_21Degree10Chunk0,boundaryRePowerRow77_21Degree10Chunk4,boundaryRePowerRow77_21Degree10Chunk8,boundaryRePowerRow77_21Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_21Degree10Chunk0Norm x).property,(boundaryRePowerRow77_21Degree10Chunk4Norm x).property,(boundaryRePowerRow77_21Degree10Chunk8Norm x).property,(boundaryRePowerRow77_21Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_21Degree10Chunk0Norm,boundaryRePowerRow77_21Degree10Chunk4Norm,boundaryRePowerRow77_21Degree10Chunk8Norm,boundaryRePowerRow77_21Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_22Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((1301807104/531441 : ℝ)) ((22-22)+2*3-6) 0 3 10 x) + (boundaryTermPowerRow77 ((-1303347200/1594323 : ℝ)) ((22-22)+2*4-6) 0 4 10 x)) + ((boundaryTermPowerRow77 ((7741010944/43046721 : ℝ)) ((22-22)+2*5-6) 0 5 10 x) + (boundaryTermPowerRow77 ((-2730161975915/99179645184 : ℝ)) ((22-22)+2*6-6) 0 6 10 x)))

def boundaryRePowerRow77_22Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_22Degree10Chunk0 x=c} := by

  have he : boundaryRePowerRow77_22Degree10Chunk0 x=boundaryRePowerRow77_22Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_22Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_22Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((10758161428625/3570467226624 : ℝ)) ((22-22)+2*7-6) 0 7 10 x) + (boundaryTermPowerRow77 ((-122502146602415/514147280633856 : ℝ)) ((22-22)+2*8-6) 0 8 10 x)) + ((boundaryTermPowerRow77 ((31394877020285/2313662762852352 : ℝ)) ((22-22)+2*9-6) 0 9 10 x) + (boundaryTermPowerRow77 ((-1094746213523575/1999004627104432128 : ℝ)) ((22-22)+2*10-6) 0 10 10 x)))

def boundaryRePowerRow77_22Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_22Degree10Chunk4 x=c} := by

  have he : boundaryRePowerRow77_22Degree10Chunk4 x=boundaryRePowerRow77_22Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_22Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_22Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((45506594977039/2998506940656648192 : ℝ)) ((22-22)+2*11-6) 0 11 10 x) + (boundaryTermPowerRow77 ((-1644097616381/5997013881313296384 : ℝ)) ((22-22)+2*12-6) 0 12 10 x)) + ((boundaryTermPowerRow77 ((80437533983/26986562465909833728 : ℝ)) ((22-22)+2*13-6) 0 13 10 x) + (boundaryTermPowerRow77 ((-940876055/53973124931819667456 : ℝ)) ((22-22)+2*14-6) 0 14 10 x)))

def boundaryRePowerRow77_22Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_22Degree10Chunk8 x=c} := by

  have he : boundaryRePowerRow77_22Degree10Chunk8 x=boundaryRePowerRow77_22Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_22Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_22Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((1277153/26986562465909833728 : ℝ)) ((22-22)+2*15-6) 0 15 10 x) + ((boundaryTermPowerRow77 ((-7765/161919374795459002368 : ℝ)) ((22-22)+2*16-6) 0 16 10 x) + (boundaryTermPowerRow77 ((25/2185911559738696531968 : ℝ)) ((22-22)+2*17-6) 0 17 10 x)))

def boundaryRePowerRow77_22Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_22Degree10Chunk12 x=c} := by

  have he : boundaryRePowerRow77_22Degree10Chunk12 x=boundaryRePowerRow77_22Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_22Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryRePowerRow77_22Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryRePowerRow77_22 10 x=c} := by

  have he : boundaryRePowerRow77_22 10 x=(((boundaryRePowerRow77_22Degree10Chunk0 x) + (boundaryRePowerRow77_22Degree10Chunk4 x)) + ((boundaryRePowerRow77_22Degree10Chunk8 x) + (boundaryRePowerRow77_22Degree10Chunk12 x))) := by

    dsimp only [boundaryRePowerRow77_22,boundaryRePowerRow77_22Degree10Chunk0,boundaryRePowerRow77_22Degree10Chunk4,boundaryRePowerRow77_22Degree10Chunk8,boundaryRePowerRow77_22Degree10Chunk12]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryRePowerRow77_22Degree10Chunk0Norm x).property,(boundaryRePowerRow77_22Degree10Chunk4Norm x).property,(boundaryRePowerRow77_22Degree10Chunk8Norm x).property,(boundaryRePowerRow77_22Degree10Chunk12Norm x).property]

    dsimp only [boundaryRePowerRow77_22Degree10Chunk0Norm,boundaryRePowerRow77_22Degree10Chunk4Norm,boundaryRePowerRow77_22Degree10Chunk8Norm,boundaryRePowerRow77_22Degree10Chunk12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((258052183/272097792 : ℝ))/3) ((21-0)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((258052183/272097792 : ℝ))/36) (((21-0)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((258052183/272097792 : ℝ))/216) (((21-0)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((6510854519/9795520512 : ℝ))/3) ((21-0)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_0Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk0 x=boundaryImPowerRow77_0Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((6510854519/9795520512 : ℝ))/36) (((21-0)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((6510854519/9795520512 : ℝ))/216) (((21-0)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-186364574969/1410554953728 : ℝ))/3) ((21-0)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-186364574969/1410554953728 : ℝ))/36) (((21-0)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_0Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk4 x=boundaryImPowerRow77_0Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-186364574969/1410554953728 : ℝ))/216) (((21-0)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-1033797574409/12694994583552 : ℝ))/3) ((21-0)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-1033797574409/12694994583552 : ℝ))/36) (((21-0)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-1033797574409/12694994583552 : ℝ))/216) (((21-0)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_0Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk8 x=boundaryImPowerRow77_0Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((12105944831381/7312316880125952 : ℝ))/3) ((21-0)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((12105944831381/7312316880125952 : ℝ))/36) (((21-0)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((12105944831381/7312316880125952 : ℝ))/216) (((21-0)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((130377163775405/65810851921133568 : ℝ))/3) ((21-0)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_0Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk12 x=boundaryImPowerRow77_0Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((130377163775405/65810851921133568 : ℝ))/36) (((21-0)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((130377163775405/65810851921133568 : ℝ))/216) (((21-0)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((284835824941/3084883683803136 : ℝ))/3) ((21-0)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((284835824941/3084883683803136 : ℝ))/36) (((21-0)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_0Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk16 x=boundaryImPowerRow77_0Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((284835824941/3084883683803136 : ℝ))/216) (((21-0)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-47428789322903/2665339502805909504 : ℝ))/3) ((21-0)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-47428789322903/2665339502805909504 : ℝ))/36) (((21-0)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-47428789322903/2665339502805909504 : ℝ))/216) (((21-0)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_0Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk20 x=boundaryImPowerRow77_0Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-9987025493561/5330679005611819008 : ℝ))/3) ((21-0)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-9987025493561/5330679005611819008 : ℝ))/36) (((21-0)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-9987025493561/5330679005611819008 : ℝ))/216) (((21-0)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((63860187804325/431784999454557339648 : ℝ))/3) ((21-0)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_0Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk24 x=boundaryImPowerRow77_0Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((63860187804325/431784999454557339648 : ℝ))/36) (((21-0)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((63860187804325/431784999454557339648 : ℝ))/216) (((21-0)+2*9-5)+2) 1 9 10 x))

def boundaryImPowerRow77_0Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_0Degree10Chunk28 x=boundaryImPowerRow77_0Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_0Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_0 10 x=c} := by

  have he : boundaryImPowerRow77_0 10 x=((((boundaryImPowerRow77_0Degree10Chunk0 x) + (boundaryImPowerRow77_0Degree10Chunk4 x)) + ((boundaryImPowerRow77_0Degree10Chunk8 x) + (boundaryImPowerRow77_0Degree10Chunk12 x))) + (((boundaryImPowerRow77_0Degree10Chunk16 x) + (boundaryImPowerRow77_0Degree10Chunk20 x)) + ((boundaryImPowerRow77_0Degree10Chunk24 x) + (boundaryImPowerRow77_0Degree10Chunk28 x)))) := by

    dsimp only [boundaryImPowerRow77_0,boundaryImPowerRow77_0Degree10Chunk0,boundaryImPowerRow77_0Degree10Chunk4,boundaryImPowerRow77_0Degree10Chunk8,boundaryImPowerRow77_0Degree10Chunk12,boundaryImPowerRow77_0Degree10Chunk16,boundaryImPowerRow77_0Degree10Chunk20,boundaryImPowerRow77_0Degree10Chunk24,boundaryImPowerRow77_0Degree10Chunk28]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_0Degree10Chunk0Norm x).property,(boundaryImPowerRow77_0Degree10Chunk4Norm x).property,(boundaryImPowerRow77_0Degree10Chunk8Norm x).property,(boundaryImPowerRow77_0Degree10Chunk12Norm x).property,(boundaryImPowerRow77_0Degree10Chunk16Norm x).property,(boundaryImPowerRow77_0Degree10Chunk20Norm x).property,(boundaryImPowerRow77_0Degree10Chunk24Norm x).property,(boundaryImPowerRow77_0Degree10Chunk28Norm x).property]

    dsimp only [boundaryImPowerRow77_0Degree10Chunk0Norm,boundaryImPowerRow77_0Degree10Chunk4Norm,boundaryImPowerRow77_0Degree10Chunk8Norm,boundaryImPowerRow77_0Degree10Chunk12Norm,boundaryImPowerRow77_0Degree10Chunk16Norm,boundaryImPowerRow77_0Degree10Chunk20Norm,boundaryImPowerRow77_0Degree10Chunk24Norm,boundaryImPowerRow77_0Degree10Chunk28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((347952563/15116544 : ℝ))/3) ((21-1)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((347952563/15116544 : ℝ))/36) (((21-1)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((347952563/15116544 : ℝ))/216) (((21-1)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((133551734933/19591041024 : ℝ))/3) ((21-1)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_1Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk0 x=boundaryImPowerRow77_1Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((133551734933/19591041024 : ℝ))/36) (((21-1)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((133551734933/19591041024 : ℝ))/216) (((21-1)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-2312978499941/470184984576 : ℝ))/3) ((21-1)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-2312978499941/470184984576 : ℝ))/36) (((21-1)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_1Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk4 x=boundaryImPowerRow77_1Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-2312978499941/470184984576 : ℝ))/216) (((21-1)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-4421341459327/5642219814912 : ℝ))/3) ((21-1)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-4421341459327/5642219814912 : ℝ))/36) (((21-1)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-4421341459327/5642219814912 : ℝ))/216) (((21-1)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_1Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk8 x=boundaryImPowerRow77_1Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((1248266550682421/7312316880125952 : ℝ))/3) ((21-1)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((1248266550682421/7312316880125952 : ℝ))/36) (((21-1)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((1248266550682421/7312316880125952 : ℝ))/216) (((21-1)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((1404956250307805/87747802561511424 : ℝ))/3) ((21-1)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_1Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk12 x=boundaryImPowerRow77_1Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((1404956250307805/87747802561511424 : ℝ))/36) (((21-1)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((1404956250307805/87747802561511424 : ℝ))/216) (((21-1)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((-3334177576970155/1184595334580404224 : ℝ))/3) ((21-1)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-3334177576970155/1184595334580404224 : ℝ))/36) (((21-1)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_1Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk16 x=boundaryImPowerRow77_1Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-3334177576970155/1184595334580404224 : ℝ))/216) (((21-1)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-293867481139519/2369190669160808448 : ℝ))/3) ((21-1)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-293867481139519/2369190669160808448 : ℝ))/36) (((21-1)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-293867481139519/2369190669160808448 : ℝ))/216) (((21-1)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_1Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk20 x=boundaryImPowerRow77_1Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((12980928713958509/191904444202025484288 : ℝ))/3) ((21-1)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((12980928713958509/191904444202025484288 : ℝ))/36) (((21-1)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((12980928713958509/191904444202025484288 : ℝ))/216) (((21-1)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-1380000928479463/215892499727278669824 : ℝ))/3) ((21-1)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_1Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk24 x=boundaryImPowerRow77_1Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-1380000928479463/215892499727278669824 : ℝ))/36) (((21-1)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-1380000928479463/215892499727278669824 : ℝ))/216) (((21-1)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((2763132821290541/15544259980364064227328 : ℝ))/3) ((21-1)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((2763132821290541/15544259980364064227328 : ℝ))/36) (((21-1)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_1Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk28 x=boundaryImPowerRow77_1Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 (7*((2763132821290541/15544259980364064227328 : ℝ))/216) (((21-1)+2*10-5)+2) 1 10 10 x)

def boundaryImPowerRow77_1Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_1Degree10Chunk32 x=boundaryImPowerRow77_1Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_1Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_1Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_1 10 x=c} := by

  have he : boundaryImPowerRow77_1 10 x=((((boundaryImPowerRow77_1Degree10Chunk0 x) + (boundaryImPowerRow77_1Degree10Chunk4 x)) + ((boundaryImPowerRow77_1Degree10Chunk8 x) + (boundaryImPowerRow77_1Degree10Chunk12 x))) + (((boundaryImPowerRow77_1Degree10Chunk16 x) + (boundaryImPowerRow77_1Degree10Chunk20 x)) + ((boundaryImPowerRow77_1Degree10Chunk24 x) + ((boundaryImPowerRow77_1Degree10Chunk28 x) + (boundaryImPowerRow77_1Degree10Chunk32 x))))) := by

    dsimp only [boundaryImPowerRow77_1,boundaryImPowerRow77_1Degree10Chunk0,boundaryImPowerRow77_1Degree10Chunk4,boundaryImPowerRow77_1Degree10Chunk8,boundaryImPowerRow77_1Degree10Chunk12,boundaryImPowerRow77_1Degree10Chunk16,boundaryImPowerRow77_1Degree10Chunk20,boundaryImPowerRow77_1Degree10Chunk24,boundaryImPowerRow77_1Degree10Chunk28,boundaryImPowerRow77_1Degree10Chunk32]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_1Degree10Chunk0Norm x).property,(boundaryImPowerRow77_1Degree10Chunk4Norm x).property,(boundaryImPowerRow77_1Degree10Chunk8Norm x).property,(boundaryImPowerRow77_1Degree10Chunk12Norm x).property,(boundaryImPowerRow77_1Degree10Chunk16Norm x).property,(boundaryImPowerRow77_1Degree10Chunk20Norm x).property,(boundaryImPowerRow77_1Degree10Chunk24Norm x).property,(boundaryImPowerRow77_1Degree10Chunk28Norm x).property,(boundaryImPowerRow77_1Degree10Chunk32Norm x).property]

    dsimp only [boundaryImPowerRow77_1Degree10Chunk0Norm,boundaryImPowerRow77_1Degree10Chunk4Norm,boundaryImPowerRow77_1Degree10Chunk8Norm,boundaryImPowerRow77_1Degree10Chunk12Norm,boundaryImPowerRow77_1Degree10Chunk16Norm,boundaryImPowerRow77_1Degree10Chunk20Norm,boundaryImPowerRow77_1Degree10Chunk24Norm,boundaryImPowerRow77_1Degree10Chunk28Norm,boundaryImPowerRow77_1Degree10Chunk32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((17921951587/90699264 : ℝ))/3) ((21-2)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((17921951587/90699264 : ℝ))/36) (((21-2)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((17921951587/90699264 : ℝ))/216) (((21-2)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-596954040563/19591041024 : ℝ))/3) ((21-2)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_2Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk0 x=boundaryImPowerRow77_2Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-596954040563/19591041024 : ℝ))/36) (((21-2)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-596954040563/19591041024 : ℝ))/216) (((21-2)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-9899750372263/235092492288 : ℝ))/3) ((21-2)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-9899750372263/235092492288 : ℝ))/36) (((21-2)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_2Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk4 x=boundaryImPowerRow77_2Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-9899750372263/235092492288 : ℝ))/216) (((21-2)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((429128690993677/101559956668416 : ℝ))/3) ((21-2)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((429128690993677/101559956668416 : ℝ))/36) (((21-2)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((429128690993677/101559956668416 : ℝ))/216) (((21-2)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_2Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk8 x=boundaryImPowerRow77_2Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((264069531291865/304679870005248 : ℝ))/3) ((21-2)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((264069531291865/304679870005248 : ℝ))/36) (((21-2)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((264069531291865/304679870005248 : ℝ))/216) (((21-2)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-7183393786654495/29249267520503808 : ℝ))/3) ((21-2)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_2Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk12 x=boundaryImPowerRow77_2Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-7183393786654495/29249267520503808 : ℝ))/36) (((21-2)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-7183393786654495/29249267520503808 : ℝ))/216) (((21-2)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((26953734167286863/3158920892214411264 : ℝ))/3) ((21-2)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((26953734167286863/3158920892214411264 : ℝ))/36) (((21-2)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_2Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk16 x=boundaryImPowerRow77_2Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((26953734167286863/3158920892214411264 : ℝ))/216) (((21-2)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((275968457834471069/42645432044894552064 : ℝ))/3) ((21-2)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((275968457834471069/42645432044894552064 : ℝ))/36) (((21-2)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((275968457834471069/42645432044894552064 : ℝ))/216) (((21-2)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_2Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk20 x=boundaryImPowerRow77_2Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-1709798571567940855/1535235553616203874304 : ℝ))/3) ((21-2)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-1709798571567940855/1535235553616203874304 : ℝ))/36) (((21-2)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-1709798571567940855/1535235553616203874304 : ℝ))/216) (((21-2)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((600569426788768079/6908559991272917434368 : ℝ))/3) ((21-2)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_2Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk24 x=boundaryImPowerRow77_2Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((600569426788768079/6908559991272917434368 : ℝ))/36) (((21-2)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((600569426788768079/6908559991272917434368 : ℝ))/216) (((21-2)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((-46690054739436401/13817119982545834868736 : ℝ))/3) ((21-2)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-46690054739436401/13817119982545834868736 : ℝ))/36) (((21-2)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_2Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk28 x=boundaryImPowerRow77_2Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-46690054739436401/13817119982545834868736 : ℝ))/216) (((21-2)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((12177572871726983/279796679646553156091904 : ℝ))/3) ((21-2)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((12177572871726983/279796679646553156091904 : ℝ))/36) (((21-2)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((12177572871726983/279796679646553156091904 : ℝ))/216) (((21-2)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_2Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_2Degree10Chunk32 x=boundaryImPowerRow77_2Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_2Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_2 10 x=c} := by

  have he : boundaryImPowerRow77_2 10 x=((((boundaryImPowerRow77_2Degree10Chunk0 x) + (boundaryImPowerRow77_2Degree10Chunk4 x)) + ((boundaryImPowerRow77_2Degree10Chunk8 x) + (boundaryImPowerRow77_2Degree10Chunk12 x))) + (((boundaryImPowerRow77_2Degree10Chunk16 x) + (boundaryImPowerRow77_2Degree10Chunk20 x)) + ((boundaryImPowerRow77_2Degree10Chunk24 x) + ((boundaryImPowerRow77_2Degree10Chunk28 x) + (boundaryImPowerRow77_2Degree10Chunk32 x))))) := by

    dsimp only [boundaryImPowerRow77_2,boundaryImPowerRow77_2Degree10Chunk0,boundaryImPowerRow77_2Degree10Chunk4,boundaryImPowerRow77_2Degree10Chunk8,boundaryImPowerRow77_2Degree10Chunk12,boundaryImPowerRow77_2Degree10Chunk16,boundaryImPowerRow77_2Degree10Chunk20,boundaryImPowerRow77_2Degree10Chunk24,boundaryImPowerRow77_2Degree10Chunk28,boundaryImPowerRow77_2Degree10Chunk32]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_2Degree10Chunk0Norm x).property,(boundaryImPowerRow77_2Degree10Chunk4Norm x).property,(boundaryImPowerRow77_2Degree10Chunk8Norm x).property,(boundaryImPowerRow77_2Degree10Chunk12Norm x).property,(boundaryImPowerRow77_2Degree10Chunk16Norm x).property,(boundaryImPowerRow77_2Degree10Chunk20Norm x).property,(boundaryImPowerRow77_2Degree10Chunk24Norm x).property,(boundaryImPowerRow77_2Degree10Chunk28Norm x).property,(boundaryImPowerRow77_2Degree10Chunk32Norm x).property]

    dsimp only [boundaryImPowerRow77_2Degree10Chunk0Norm,boundaryImPowerRow77_2Degree10Chunk4Norm,boundaryImPowerRow77_2Degree10Chunk8Norm,boundaryImPowerRow77_2Degree10Chunk12Norm,boundaryImPowerRow77_2Degree10Chunk16Norm,boundaryImPowerRow77_2Degree10Chunk20Norm,boundaryImPowerRow77_2Degree10Chunk24Norm,boundaryImPowerRow77_2Degree10Chunk28Norm,boundaryImPowerRow77_2Degree10Chunk32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((4433739133/8503056 : ℝ))/3) ((21-3)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((4433739133/8503056 : ℝ))/36) (((21-3)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((4433739133/8503056 : ℝ))/216) (((21-3)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-5748284649001/9795520512 : ℝ))/3) ((21-3)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_3Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk0 x=boundaryImPowerRow77_3Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-5748284649001/9795520512 : ℝ))/36) (((21-3)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-5748284649001/9795520512 : ℝ))/216) (((21-3)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-25425160016345/1410554953728 : ℝ))/3) ((21-3)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-25425160016345/1410554953728 : ℝ))/36) (((21-3)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_3Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk4 x=boundaryImPowerRow77_3Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-25425160016345/1410554953728 : ℝ))/216) (((21-3)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((3798237873321137/101559956668416 : ℝ))/3) ((21-3)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((3798237873321137/101559956668416 : ℝ))/36) (((21-3)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((3798237873321137/101559956668416 : ℝ))/216) (((21-3)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_3Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk8 x=boundaryImPowerRow77_3Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-36297245462526875/3656158440062976 : ℝ))/3) ((21-3)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-36297245462526875/3656158440062976 : ℝ))/36) (((21-3)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-36297245462526875/3656158440062976 : ℝ))/216) (((21-3)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((5189128058942131/14624633760251904 : ℝ))/3) ((21-3)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_3Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk12 x=boundaryImPowerRow77_3Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((5189128058942131/14624633760251904 : ℝ))/36) (((21-3)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((5189128058942131/14624633760251904 : ℝ))/216) (((21-3)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((5839049016890081813/18953525353286467584 : ℝ))/3) ((21-3)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((5839049016890081813/18953525353286467584 : ℝ))/36) (((21-3)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_3Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk16 x=boundaryImPowerRow77_3Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((5839049016890081813/18953525353286467584 : ℝ))/216) (((21-3)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-85389012600265476499/1364653825436625666048 : ℝ))/3) ((21-3)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-85389012600265476499/1364653825436625666048 : ℝ))/36) (((21-3)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-85389012600265476499/1364653825436625666048 : ℝ))/216) (((21-3)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_3Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk20 x=boundaryImPowerRow77_3Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((9824350396117451999/1535235553616203874304 : ℝ))/3) ((21-3)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((9824350396117451999/1535235553616203874304 : ℝ))/36) (((21-3)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((9824350396117451999/1535235553616203874304 : ℝ))/216) (((21-3)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-5056817636319640633/12281884428929630994432 : ℝ))/3) ((21-3)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_3Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk24 x=boundaryImPowerRow77_3Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-5056817636319640633/12281884428929630994432 : ℝ))/36) (((21-3)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-5056817636319640633/12281884428929630994432 : ℝ))/216) (((21-3)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((6199201151966658827/331610879581100036849664 : ℝ))/3) ((21-3)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((6199201151966658827/331610879581100036849664 : ℝ))/36) (((21-3)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_3Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk28 x=boundaryImPowerRow77_3Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((6199201151966658827/331610879581100036849664 : ℝ))/216) (((21-3)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-131755225973988043/279796679646553156091904 : ℝ))/3) ((21-3)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-131755225973988043/279796679646553156091904 : ℝ))/36) (((21-3)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-131755225973988043/279796679646553156091904 : ℝ))/216) (((21-3)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_3Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk32 x=boundaryImPowerRow77_3Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (((259263771223410611/80581443738207308954468352 : ℝ))/3) ((21-3)+2*12-5) 0 12 10 x) + ((boundaryTermPowerRow77 (-((259263771223410611/80581443738207308954468352 : ℝ))/36) (((21-3)+2*12-5)+1) 1 12 10 x) + (boundaryTermPowerRow77 (7*((259263771223410611/80581443738207308954468352 : ℝ))/216) (((21-3)+2*12-5)+2) 1 12 10 x)))

def boundaryImPowerRow77_3Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_3Degree10Chunk36 x=boundaryImPowerRow77_3Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_3Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_3 10 x=c} := by

  have he : boundaryImPowerRow77_3 10 x=((((boundaryImPowerRow77_3Degree10Chunk0 x) + (boundaryImPowerRow77_3Degree10Chunk4 x)) + ((boundaryImPowerRow77_3Degree10Chunk8 x) + ((boundaryImPowerRow77_3Degree10Chunk12 x) + (boundaryImPowerRow77_3Degree10Chunk16 x)))) + (((boundaryImPowerRow77_3Degree10Chunk20 x) + (boundaryImPowerRow77_3Degree10Chunk24 x)) + ((boundaryImPowerRow77_3Degree10Chunk28 x) + ((boundaryImPowerRow77_3Degree10Chunk32 x) + (boundaryImPowerRow77_3Degree10Chunk36 x))))) := by

    dsimp only [boundaryImPowerRow77_3,boundaryImPowerRow77_3Degree10Chunk0,boundaryImPowerRow77_3Degree10Chunk4,boundaryImPowerRow77_3Degree10Chunk8,boundaryImPowerRow77_3Degree10Chunk12,boundaryImPowerRow77_3Degree10Chunk16,boundaryImPowerRow77_3Degree10Chunk20,boundaryImPowerRow77_3Degree10Chunk24,boundaryImPowerRow77_3Degree10Chunk28,boundaryImPowerRow77_3Degree10Chunk32,boundaryImPowerRow77_3Degree10Chunk36]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_3Degree10Chunk0Norm x).property,(boundaryImPowerRow77_3Degree10Chunk4Norm x).property,(boundaryImPowerRow77_3Degree10Chunk8Norm x).property,(boundaryImPowerRow77_3Degree10Chunk12Norm x).property,(boundaryImPowerRow77_3Degree10Chunk16Norm x).property,(boundaryImPowerRow77_3Degree10Chunk20Norm x).property,(boundaryImPowerRow77_3Degree10Chunk24Norm x).property,(boundaryImPowerRow77_3Degree10Chunk28Norm x).property,(boundaryImPowerRow77_3Degree10Chunk32Norm x).property,(boundaryImPowerRow77_3Degree10Chunk36Norm x).property]

    dsimp only [boundaryImPowerRow77_3Degree10Chunk0Norm,boundaryImPowerRow77_3Degree10Chunk4Norm,boundaryImPowerRow77_3Degree10Chunk8Norm,boundaryImPowerRow77_3Degree10Chunk12Norm,boundaryImPowerRow77_3Degree10Chunk16Norm,boundaryImPowerRow77_3Degree10Chunk20Norm,boundaryImPowerRow77_3Degree10Chunk24Norm,boundaryImPowerRow77_3Degree10Chunk28Norm,boundaryImPowerRow77_3Degree10Chunk32Norm,boundaryImPowerRow77_3Degree10Chunk36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-526010560219/272097792 : ℝ))/3) ((21-4)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-526010560219/272097792 : ℝ))/36) (((21-4)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-526010560219/272097792 : ℝ))/216) (((21-4)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-30790866766487/19591041024 : ℝ))/3) ((21-4)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_4Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk0 x=boundaryImPowerRow77_4Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-30790866766487/19591041024 : ℝ))/36) (((21-4)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-30790866766487/19591041024 : ℝ))/216) (((21-4)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((108460793539765/156728328192 : ℝ))/3) ((21-4)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((108460793539765/156728328192 : ℝ))/36) (((21-4)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_4Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk4 x=boundaryImPowerRow77_4Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((108460793539765/156728328192 : ℝ))/216) (((21-4)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-1052275049253833/6347497291776 : ℝ))/3) ((21-4)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-1052275049253833/6347497291776 : ℝ))/36) (((21-4)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-1052275049253833/6347497291776 : ℝ))/216) (((21-4)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_4Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk8 x=boundaryImPowerRow77_4Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-24190683190474379/7312316880125952 : ℝ))/3) ((21-4)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-24190683190474379/7312316880125952 : ℝ))/36) (((21-4)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-24190683190474379/7312316880125952 : ℝ))/216) (((21-4)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((768886023267285253/65810851921133568 : ℝ))/3) ((21-4)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_4Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk12 x=boundaryImPowerRow77_4Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((768886023267285253/65810851921133568 : ℝ))/36) (((21-4)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((768886023267285253/65810851921133568 : ℝ))/216) (((21-4)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((-87324025383315097261/37907050706572935168 : ℝ))/3) ((21-4)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-87324025383315097261/37907050706572935168 : ℝ))/36) (((21-4)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_4Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk16 x=boundaryImPowerRow77_4Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-87324025383315097261/37907050706572935168 : ℝ))/216) (((21-4)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((245316404231561318377/1364653825436625666048 : ℝ))/3) ((21-4)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((245316404231561318377/1364653825436625666048 : ℝ))/36) (((21-4)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((245316404231561318377/1364653825436625666048 : ℝ))/216) (((21-4)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_4Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk20 x=boundaryImPowerRow77_4Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-326519775830088756265/196510150862874095910912 : ℝ))/3) ((21-4)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-326519775830088756265/196510150862874095910912 : ℝ))/36) (((21-4)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-326519775830088756265/196510150862874095910912 : ℝ))/216) (((21-4)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-917970537207242003641/1768591357765866863198208 : ℝ))/3) ((21-4)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_4Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk24 x=boundaryImPowerRow77_4Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-917970537207242003641/1768591357765866863198208 : ℝ))/36) (((21-4)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-917970537207242003641/1768591357765866863198208 : ℝ))/216) (((21-4)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((15082768023679164271/884295678882933431599104 : ℝ))/3) ((21-4)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((15082768023679164271/884295678882933431599104 : ℝ))/36) (((21-4)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_4Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk28 x=boundaryImPowerRow77_4Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((15082768023679164271/884295678882933431599104 : ℝ))/216) (((21-4)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((43897479471302461307/71627949989517607959527424 : ℝ))/3) ((21-4)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((43897479471302461307/71627949989517607959527424 : ℝ))/36) (((21-4)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((43897479471302461307/71627949989517607959527424 : ℝ))/216) (((21-4)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_4Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk32 x=boundaryImPowerRow77_4Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-25566620683021306693/1289303099811316943271493632 : ℝ))/3) ((21-4)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-25566620683021306693/1289303099811316943271493632 : ℝ))/36) (((21-4)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-25566620683021306693/1289303099811316943271493632 : ℝ))/216) (((21-4)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((308296208412382897/3867909299433950829814480896 : ℝ))/3) ((21-4)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_4Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk36 x=boundaryImPowerRow77_4Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((308296208412382897/3867909299433950829814480896 : ℝ))/36) (((21-4)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((308296208412382897/3867909299433950829814480896 : ℝ))/216) (((21-4)+2*13-5)+2) 1 13 10 x))

def boundaryImPowerRow77_4Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_4Degree10Chunk40 x=boundaryImPowerRow77_4Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_4Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_4Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_4 10 x=c} := by

  have he : boundaryImPowerRow77_4 10 x=((((boundaryImPowerRow77_4Degree10Chunk0 x) + (boundaryImPowerRow77_4Degree10Chunk4 x)) + ((boundaryImPowerRow77_4Degree10Chunk8 x) + ((boundaryImPowerRow77_4Degree10Chunk12 x) + (boundaryImPowerRow77_4Degree10Chunk16 x)))) + (((boundaryImPowerRow77_4Degree10Chunk20 x) + ((boundaryImPowerRow77_4Degree10Chunk24 x) + (boundaryImPowerRow77_4Degree10Chunk28 x))) + ((boundaryImPowerRow77_4Degree10Chunk32 x) + ((boundaryImPowerRow77_4Degree10Chunk36 x) + (boundaryImPowerRow77_4Degree10Chunk40 x))))) := by

    dsimp only [boundaryImPowerRow77_4,boundaryImPowerRow77_4Degree10Chunk0,boundaryImPowerRow77_4Degree10Chunk4,boundaryImPowerRow77_4Degree10Chunk8,boundaryImPowerRow77_4Degree10Chunk12,boundaryImPowerRow77_4Degree10Chunk16,boundaryImPowerRow77_4Degree10Chunk20,boundaryImPowerRow77_4Degree10Chunk24,boundaryImPowerRow77_4Degree10Chunk28,boundaryImPowerRow77_4Degree10Chunk32,boundaryImPowerRow77_4Degree10Chunk36,boundaryImPowerRow77_4Degree10Chunk40]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_4Degree10Chunk0Norm x).property,(boundaryImPowerRow77_4Degree10Chunk4Norm x).property,(boundaryImPowerRow77_4Degree10Chunk8Norm x).property,(boundaryImPowerRow77_4Degree10Chunk12Norm x).property,(boundaryImPowerRow77_4Degree10Chunk16Norm x).property,(boundaryImPowerRow77_4Degree10Chunk20Norm x).property,(boundaryImPowerRow77_4Degree10Chunk24Norm x).property,(boundaryImPowerRow77_4Degree10Chunk28Norm x).property,(boundaryImPowerRow77_4Degree10Chunk32Norm x).property,(boundaryImPowerRow77_4Degree10Chunk36Norm x).property,(boundaryImPowerRow77_4Degree10Chunk40Norm x).property]

    dsimp only [boundaryImPowerRow77_4Degree10Chunk0Norm,boundaryImPowerRow77_4Degree10Chunk4Norm,boundaryImPowerRow77_4Degree10Chunk8Norm,boundaryImPowerRow77_4Degree10Chunk12Norm,boundaryImPowerRow77_4Degree10Chunk16Norm,boundaryImPowerRow77_4Degree10Chunk20Norm,boundaryImPowerRow77_4Degree10Chunk24Norm,boundaryImPowerRow77_4Degree10Chunk28Norm,boundaryImPowerRow77_4Degree10Chunk32Norm,boundaryImPowerRow77_4Degree10Chunk36Norm,boundaryImPowerRow77_4Degree10Chunk40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-595134447329/45349632 : ℝ))/3) ((21-5)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-595134447329/45349632 : ℝ))/36) (((21-5)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-595134447329/45349632 : ℝ))/216) (((21-5)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((68246754478747/19591041024 : ℝ))/3) ((21-5)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_5Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk0 x=boundaryImPowerRow77_5Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((68246754478747/19591041024 : ℝ))/36) (((21-5)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((68246754478747/19591041024 : ℝ))/216) (((21-5)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-139280847775457/235092492288 : ℝ))/3) ((21-5)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-139280847775457/235092492288 : ℝ))/36) (((21-5)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_5Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk4 x=boundaryImPowerRow77_5Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-139280847775457/235092492288 : ℝ))/216) (((21-5)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-653806045063829/1586874322944 : ℝ))/3) ((21-5)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-653806045063829/1586874322944 : ℝ))/36) (((21-5)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-653806045063829/1586874322944 : ℝ))/216) (((21-5)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_5Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk8 x=boundaryImPowerRow77_5Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((576135055035147667/1828079220031488 : ℝ))/3) ((21-5)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((576135055035147667/1828079220031488 : ℝ))/36) (((21-5)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((576135055035147667/1828079220031488 : ℝ))/216) (((21-5)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-30144349061698426627/526486815369068544 : ℝ))/3) ((21-5)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_5Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk12 x=boundaryImPowerRow77_5Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-30144349061698426627/526486815369068544 : ℝ))/36) (((21-5)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-30144349061698426627/526486815369068544 : ℝ))/216) (((21-5)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((8535111205340920181/4211894522952548352 : ℝ))/3) ((21-5)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((8535111205340920181/4211894522952548352 : ℝ))/36) (((21-5)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_5Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk16 x=boundaryImPowerRow77_5Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((8535111205340920181/4211894522952548352 : ℝ))/216) (((21-5)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((87540653190844684615/113721152119718805504 : ℝ))/3) ((21-5)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((87540653190844684615/113721152119718805504 : ℝ))/36) (((21-5)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((87540653190844684615/113721152119718805504 : ℝ))/216) (((21-5)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_5Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk20 x=boundaryImPowerRow77_5Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-27755368091845695374635/196510150862874095910912 : ℝ))/3) ((21-5)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-27755368091845695374635/196510150862874095910912 : ℝ))/36) (((21-5)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-27755368091845695374635/196510150862874095910912 : ℝ))/216) (((21-5)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((6713613650610981410789/589530452588622287732736 : ℝ))/3) ((21-5)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_5Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk24 x=boundaryImPowerRow77_5Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((6713613650610981410789/589530452588622287732736 : ℝ))/36) (((21-5)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((6713613650610981410789/589530452588622287732736 : ℝ))/216) (((21-5)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((-1959259070331909946855/3979330554973200442195968 : ℝ))/3) ((21-5)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-1959259070331909946855/3979330554973200442195968 : ℝ))/36) (((21-5)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_5Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk28 x=boundaryImPowerRow77_5Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-1959259070331909946855/3979330554973200442195968 : ℝ))/216) (((21-5)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((701417487728543150753/71627949989517607959527424 : ℝ))/3) ((21-5)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((701417487728543150753/71627949989517607959527424 : ℝ))/36) (((21-5)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((701417487728543150753/71627949989517607959527424 : ℝ))/216) (((21-5)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_5Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk32 x=boundaryImPowerRow77_5Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-53871599646351098255/1289303099811316943271493632 : ℝ))/3) ((21-5)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-53871599646351098255/1289303099811316943271493632 : ℝ))/36) (((21-5)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-53871599646351098255/1289303099811316943271493632 : ℝ))/216) (((21-5)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-2666267823376143329/11603727898301852489443442688 : ℝ))/3) ((21-5)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_5Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk36 x=boundaryImPowerRow77_5Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-2666267823376143329/11603727898301852489443442688 : ℝ))/36) (((21-5)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-2666267823376143329/11603727898301852489443442688 : ℝ))/216) (((21-5)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((33325770944820067/52216775542358336202495492096 : ℝ))/3) ((21-5)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((33325770944820067/52216775542358336202495492096 : ℝ))/36) (((21-5)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_5Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk40 x=boundaryImPowerRow77_5Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 (7*((33325770944820067/52216775542358336202495492096 : ℝ))/216) (((21-5)+2*14-5)+2) 1 14 10 x)

def boundaryImPowerRow77_5Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_5Degree10Chunk44 x=boundaryImPowerRow77_5Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_5Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_5 10 x=c} := by

  have he : boundaryImPowerRow77_5 10 x=((((boundaryImPowerRow77_5Degree10Chunk0 x) + ((boundaryImPowerRow77_5Degree10Chunk4 x) + (boundaryImPowerRow77_5Degree10Chunk8 x))) + ((boundaryImPowerRow77_5Degree10Chunk12 x) + ((boundaryImPowerRow77_5Degree10Chunk16 x) + (boundaryImPowerRow77_5Degree10Chunk20 x)))) + (((boundaryImPowerRow77_5Degree10Chunk24 x) + ((boundaryImPowerRow77_5Degree10Chunk28 x) + (boundaryImPowerRow77_5Degree10Chunk32 x))) + ((boundaryImPowerRow77_5Degree10Chunk36 x) + ((boundaryImPowerRow77_5Degree10Chunk40 x) + (boundaryImPowerRow77_5Degree10Chunk44 x))))) := by

    dsimp only [boundaryImPowerRow77_5,boundaryImPowerRow77_5Degree10Chunk0,boundaryImPowerRow77_5Degree10Chunk4,boundaryImPowerRow77_5Degree10Chunk8,boundaryImPowerRow77_5Degree10Chunk12,boundaryImPowerRow77_5Degree10Chunk16,boundaryImPowerRow77_5Degree10Chunk20,boundaryImPowerRow77_5Degree10Chunk24,boundaryImPowerRow77_5Degree10Chunk28,boundaryImPowerRow77_5Degree10Chunk32,boundaryImPowerRow77_5Degree10Chunk36,boundaryImPowerRow77_5Degree10Chunk40,boundaryImPowerRow77_5Degree10Chunk44]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_5Degree10Chunk0Norm x).property,(boundaryImPowerRow77_5Degree10Chunk4Norm x).property,(boundaryImPowerRow77_5Degree10Chunk8Norm x).property,(boundaryImPowerRow77_5Degree10Chunk12Norm x).property,(boundaryImPowerRow77_5Degree10Chunk16Norm x).property,(boundaryImPowerRow77_5Degree10Chunk20Norm x).property,(boundaryImPowerRow77_5Degree10Chunk24Norm x).property,(boundaryImPowerRow77_5Degree10Chunk28Norm x).property,(boundaryImPowerRow77_5Degree10Chunk32Norm x).property,(boundaryImPowerRow77_5Degree10Chunk36Norm x).property,(boundaryImPowerRow77_5Degree10Chunk40Norm x).property,(boundaryImPowerRow77_5Degree10Chunk44Norm x).property]

    dsimp only [boundaryImPowerRow77_5Degree10Chunk0Norm,boundaryImPowerRow77_5Degree10Chunk4Norm,boundaryImPowerRow77_5Degree10Chunk8Norm,boundaryImPowerRow77_5Degree10Chunk12Norm,boundaryImPowerRow77_5Degree10Chunk16Norm,boundaryImPowerRow77_5Degree10Chunk20Norm,boundaryImPowerRow77_5Degree10Chunk24Norm,boundaryImPowerRow77_5Degree10Chunk28Norm,boundaryImPowerRow77_5Degree10Chunk32Norm,boundaryImPowerRow77_5Degree10Chunk36Norm,boundaryImPowerRow77_5Degree10Chunk40Norm,boundaryImPowerRow77_5Degree10Chunk44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-435529901581/30233088 : ℝ))/3) ((21-6)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-435529901581/30233088 : ℝ))/36) (((21-6)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-435529901581/30233088 : ℝ))/216) (((21-6)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((21079894651837/3265173504 : ℝ))/3) ((21-6)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_6Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk0 x=boundaryImPowerRow77_6Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((21079894651837/3265173504 : ℝ))/36) (((21-6)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((21079894651837/3265173504 : ℝ))/216) (((21-6)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-9224477539639031/1410554953728 : ℝ))/3) ((21-6)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-9224477539639031/1410554953728 : ℝ))/36) (((21-6)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_6Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk4 x=boundaryImPowerRow77_6Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-9224477539639031/1410554953728 : ℝ))/216) (((21-6)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((124313652617230921/25389989167104 : ℝ))/3) ((21-6)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((124313652617230921/25389989167104 : ℝ))/36) (((21-6)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((124313652617230921/25389989167104 : ℝ))/216) (((21-6)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_6Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk8 x=boundaryImPowerRow77_6Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-927716298309686179/1218719480020992 : ℝ))/3) ((21-6)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-927716298309686179/1218719480020992 : ℝ))/36) (((21-6)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-927716298309686179/1218719480020992 : ℝ))/216) (((21-6)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-33720799191539834227/526486815369068544 : ℝ))/3) ((21-6)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_6Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk12 x=boundaryImPowerRow77_6Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-33720799191539834227/526486815369068544 : ℝ))/36) (((21-6)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-33720799191539834227/526486815369068544 : ℝ))/216) (((21-6)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((1513072156662829446371/37907050706572935168 : ℝ))/3) ((21-6)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((1513072156662829446371/37907050706572935168 : ℝ))/36) (((21-6)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_6Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk16 x=boundaryImPowerRow77_6Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((1513072156662829446371/37907050706572935168 : ℝ))/216) (((21-6)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-18092585090551991507689/2729307650873251332096 : ℝ))/3) ((21-6)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-18092585090551991507689/2729307650873251332096 : ℝ))/36) (((21-6)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-18092585090551991507689/2729307650873251332096 : ℝ))/216) (((21-6)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_6Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk20 x=boundaryImPowerRow77_6Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((28957134332878925827015/49127537715718523977728 : ℝ))/3) ((21-6)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((28957134332878925827015/49127537715718523977728 : ℝ))/36) (((21-6)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((28957134332878925827015/49127537715718523977728 : ℝ))/216) (((21-6)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-19521058616475826326175/589530452588622287732736 : ℝ))/3) ((21-6)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_6Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk24 x=boundaryImPowerRow77_6Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-19521058616475826326175/589530452588622287732736 : ℝ))/36) (((21-6)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-19521058616475826326175/589530452588622287732736 : ℝ))/216) (((21-6)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((2685120561813462228287/1989665277486600221097984 : ℝ))/3) ((21-6)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((2685120561813462228287/1989665277486600221097984 : ℝ))/36) (((21-6)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_6Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk28 x=boundaryImPowerRow77_6Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((2685120561813462228287/1989665277486600221097984 : ℝ))/216) (((21-6)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-2773143382194760538135/71627949989517607959527424 : ℝ))/3) ((21-6)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-2773143382194760538135/71627949989517607959527424 : ℝ))/36) (((21-6)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-2773143382194760538135/71627949989517607959527424 : ℝ))/216) (((21-6)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_6Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk32 x=boundaryImPowerRow77_6Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((3316585657773002819/6715120311517275746205696 : ℝ))/3) ((21-6)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((3316585657773002819/6715120311517275746205696 : ℝ))/36) (((21-6)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((3316585657773002819/6715120311517275746205696 : ℝ))/216) (((21-6)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-18870706190402301557/11603727898301852489443442688 : ℝ))/3) ((21-6)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_6Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk36 x=boundaryImPowerRow77_6Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-18870706190402301557/11603727898301852489443442688 : ℝ))/36) (((21-6)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-18870706190402301557/11603727898301852489443442688 : ℝ))/216) (((21-6)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((-7005682798896131/26108387771179168101247746048 : ℝ))/3) ((21-6)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((-7005682798896131/26108387771179168101247746048 : ℝ))/36) (((21-6)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_6Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk40 x=boundaryImPowerRow77_6Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-7005682798896131/26108387771179168101247746048 : ℝ))/216) (((21-6)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((20228983537427/14685968121288282056951857152 : ℝ))/3) ((21-6)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((20228983537427/14685968121288282056951857152 : ℝ))/36) (((21-6)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((20228983537427/14685968121288282056951857152 : ℝ))/216) (((21-6)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_6Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_6Degree10Chunk44 x=boundaryImPowerRow77_6Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_6Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_6 10 x=c} := by

  have he : boundaryImPowerRow77_6 10 x=((((boundaryImPowerRow77_6Degree10Chunk0 x) + ((boundaryImPowerRow77_6Degree10Chunk4 x) + (boundaryImPowerRow77_6Degree10Chunk8 x))) + ((boundaryImPowerRow77_6Degree10Chunk12 x) + ((boundaryImPowerRow77_6Degree10Chunk16 x) + (boundaryImPowerRow77_6Degree10Chunk20 x)))) + (((boundaryImPowerRow77_6Degree10Chunk24 x) + ((boundaryImPowerRow77_6Degree10Chunk28 x) + (boundaryImPowerRow77_6Degree10Chunk32 x))) + ((boundaryImPowerRow77_6Degree10Chunk36 x) + ((boundaryImPowerRow77_6Degree10Chunk40 x) + (boundaryImPowerRow77_6Degree10Chunk44 x))))) := by

    dsimp only [boundaryImPowerRow77_6,boundaryImPowerRow77_6Degree10Chunk0,boundaryImPowerRow77_6Degree10Chunk4,boundaryImPowerRow77_6Degree10Chunk8,boundaryImPowerRow77_6Degree10Chunk12,boundaryImPowerRow77_6Degree10Chunk16,boundaryImPowerRow77_6Degree10Chunk20,boundaryImPowerRow77_6Degree10Chunk24,boundaryImPowerRow77_6Degree10Chunk28,boundaryImPowerRow77_6Degree10Chunk32,boundaryImPowerRow77_6Degree10Chunk36,boundaryImPowerRow77_6Degree10Chunk40,boundaryImPowerRow77_6Degree10Chunk44]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_6Degree10Chunk0Norm x).property,(boundaryImPowerRow77_6Degree10Chunk4Norm x).property,(boundaryImPowerRow77_6Degree10Chunk8Norm x).property,(boundaryImPowerRow77_6Degree10Chunk12Norm x).property,(boundaryImPowerRow77_6Degree10Chunk16Norm x).property,(boundaryImPowerRow77_6Degree10Chunk20Norm x).property,(boundaryImPowerRow77_6Degree10Chunk24Norm x).property,(boundaryImPowerRow77_6Degree10Chunk28Norm x).property,(boundaryImPowerRow77_6Degree10Chunk32Norm x).property,(boundaryImPowerRow77_6Degree10Chunk36Norm x).property,(boundaryImPowerRow77_6Degree10Chunk40Norm x).property,(boundaryImPowerRow77_6Degree10Chunk44Norm x).property]

    dsimp only [boundaryImPowerRow77_6Degree10Chunk0Norm,boundaryImPowerRow77_6Degree10Chunk4Norm,boundaryImPowerRow77_6Degree10Chunk8Norm,boundaryImPowerRow77_6Degree10Chunk12Norm,boundaryImPowerRow77_6Degree10Chunk16Norm,boundaryImPowerRow77_6Degree10Chunk20Norm,boundaryImPowerRow77_6Degree10Chunk24Norm,boundaryImPowerRow77_6Degree10Chunk28Norm,boundaryImPowerRow77_6Degree10Chunk32Norm,boundaryImPowerRow77_6Degree10Chunk36Norm,boundaryImPowerRow77_6Degree10Chunk40Norm,boundaryImPowerRow77_6Degree10Chunk44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((6485976127/354294 : ℝ))/3) ((21-7)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((6485976127/354294 : ℝ))/36) (((21-7)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((6485976127/354294 : ℝ))/216) (((21-7)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-1512397466611/51018336 : ℝ))/3) ((21-7)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_7Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk0 x=boundaryImPowerRow77_7Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-1512397466611/51018336 : ℝ))/36) (((21-7)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-1512397466611/51018336 : ℝ))/216) (((21-7)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((55906294622035723/1410554953728 : ℝ))/3) ((21-7)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((55906294622035723/1410554953728 : ℝ))/36) (((21-7)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_7Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk4 x=boundaryImPowerRow77_7Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((55906294622035723/1410554953728 : ℝ))/216) (((21-7)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-93733933937039437/50779978334208 : ℝ))/3) ((21-7)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-93733933937039437/50779978334208 : ℝ))/36) (((21-7)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-93733933937039437/50779978334208 : ℝ))/216) (((21-7)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_7Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk8 x=boundaryImPowerRow77_7Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-11873006041514127179/3656158440062976 : ℝ))/3) ((21-7)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-11873006041514127179/3656158440062976 : ℝ))/36) (((21-7)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-11873006041514127179/3656158440062976 : ℝ))/216) (((21-7)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((188763308079355258709/175495605123022848 : ℝ))/3) ((21-7)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_7Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk12 x=boundaryImPowerRow77_7Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((188763308079355258709/175495605123022848 : ℝ))/36) (((21-7)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((188763308079355258709/175495605123022848 : ℝ))/216) (((21-7)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((-1056501236337848358445/6317841784428822528 : ℝ))/3) ((21-7)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-1056501236337848358445/6317841784428822528 : ℝ))/36) (((21-7)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_7Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk16 x=boundaryImPowerRow77_7Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-1056501236337848358445/6317841784428822528 : ℝ))/216) (((21-7)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((34718044567770180348823/2729307650873251332096 : ℝ))/3) ((21-7)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((34718044567770180348823/2729307650873251332096 : ℝ))/36) (((21-7)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((34718044567770180348823/2729307650873251332096 : ℝ))/216) (((21-7)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_7Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk20 x=boundaryImPowerRow77_7Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-389889974090594344295/1535235553616203874304 : ℝ))/3) ((21-7)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-389889974090594344295/1535235553616203874304 : ℝ))/36) (((21-7)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-389889974090594344295/1535235553616203874304 : ℝ))/216) (((21-7)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-14944578412970495446663/589530452588622287732736 : ℝ))/3) ((21-7)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_7Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk24 x=boundaryImPowerRow77_7Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-14944578412970495446663/589530452588622287732736 : ℝ))/36) (((21-7)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-14944578412970495446663/589530452588622287732736 : ℝ))/216) (((21-7)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((1035895688294606674283/663221759162200073699328 : ℝ))/3) ((21-7)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((1035895688294606674283/663221759162200073699328 : ℝ))/36) (((21-7)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_7Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk28 x=boundaryImPowerRow77_7Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((1035895688294606674283/663221759162200073699328 : ℝ))/216) (((21-7)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-52287251018809068667/3979330554973200442195968 : ℝ))/3) ((21-7)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-52287251018809068667/3979330554973200442195968 : ℝ))/36) (((21-7)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-52287251018809068667/3979330554973200442195968 : ℝ))/216) (((21-7)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_7Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk32 x=boundaryImPowerRow77_7Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-13428613985746398665/23875983329839202653175808 : ℝ))/3) ((21-7)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-13428613985746398665/23875983329839202653175808 : ℝ))/36) (((21-7)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-13428613985746398665/23875983329839202653175808 : ℝ))/216) (((21-7)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((24801621332876898391/3867909299433950829814480896 : ℝ))/3) ((21-7)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_7Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk36 x=boundaryImPowerRow77_7Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((24801621332876898391/3867909299433950829814480896 : ℝ))/36) (((21-7)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((24801621332876898391/3867909299433950829814480896 : ℝ))/216) (((21-7)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((-220215020591630995/17405591847452778734165164032 : ℝ))/3) ((21-7)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((-220215020591630995/17405591847452778734165164032 : ℝ))/36) (((21-7)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_7Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk40 x=boundaryImPowerRow77_7Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-220215020591630995/17405591847452778734165164032 : ℝ))/216) (((21-7)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((432407062850917/234975489940612512911229714432 : ℝ))/3) ((21-7)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((432407062850917/234975489940612512911229714432 : ℝ))/36) (((21-7)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((432407062850917/234975489940612512911229714432 : ℝ))/216) (((21-7)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_7Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk44 x=boundaryImPowerRow77_7Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (((121763303179/264347426183189077025133428736 : ℝ))/3) ((21-7)+2*16-5) 0 16 10 x) + ((boundaryTermPowerRow77 (-((121763303179/264347426183189077025133428736 : ℝ))/36) (((21-7)+2*16-5)+1) 1 16 10 x) + (boundaryTermPowerRow77 (7*((121763303179/264347426183189077025133428736 : ℝ))/216) (((21-7)+2*16-5)+2) 1 16 10 x)))

def boundaryImPowerRow77_7Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_7Degree10Chunk48 x=boundaryImPowerRow77_7Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_7Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_7Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_7 10 x=c} := by

  have he : boundaryImPowerRow77_7 10 x=((((boundaryImPowerRow77_7Degree10Chunk0 x) + ((boundaryImPowerRow77_7Degree10Chunk4 x) + (boundaryImPowerRow77_7Degree10Chunk8 x))) + ((boundaryImPowerRow77_7Degree10Chunk12 x) + ((boundaryImPowerRow77_7Degree10Chunk16 x) + (boundaryImPowerRow77_7Degree10Chunk20 x)))) + (((boundaryImPowerRow77_7Degree10Chunk24 x) + ((boundaryImPowerRow77_7Degree10Chunk28 x) + (boundaryImPowerRow77_7Degree10Chunk32 x))) + (((boundaryImPowerRow77_7Degree10Chunk36 x) + (boundaryImPowerRow77_7Degree10Chunk40 x)) + ((boundaryImPowerRow77_7Degree10Chunk44 x) + (boundaryImPowerRow77_7Degree10Chunk48 x))))) := by

    dsimp only [boundaryImPowerRow77_7,boundaryImPowerRow77_7Degree10Chunk0,boundaryImPowerRow77_7Degree10Chunk4,boundaryImPowerRow77_7Degree10Chunk8,boundaryImPowerRow77_7Degree10Chunk12,boundaryImPowerRow77_7Degree10Chunk16,boundaryImPowerRow77_7Degree10Chunk20,boundaryImPowerRow77_7Degree10Chunk24,boundaryImPowerRow77_7Degree10Chunk28,boundaryImPowerRow77_7Degree10Chunk32,boundaryImPowerRow77_7Degree10Chunk36,boundaryImPowerRow77_7Degree10Chunk40,boundaryImPowerRow77_7Degree10Chunk44,boundaryImPowerRow77_7Degree10Chunk48]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_7Degree10Chunk0Norm x).property,(boundaryImPowerRow77_7Degree10Chunk4Norm x).property,(boundaryImPowerRow77_7Degree10Chunk8Norm x).property,(boundaryImPowerRow77_7Degree10Chunk12Norm x).property,(boundaryImPowerRow77_7Degree10Chunk16Norm x).property,(boundaryImPowerRow77_7Degree10Chunk20Norm x).property,(boundaryImPowerRow77_7Degree10Chunk24Norm x).property,(boundaryImPowerRow77_7Degree10Chunk28Norm x).property,(boundaryImPowerRow77_7Degree10Chunk32Norm x).property,(boundaryImPowerRow77_7Degree10Chunk36Norm x).property,(boundaryImPowerRow77_7Degree10Chunk40Norm x).property,(boundaryImPowerRow77_7Degree10Chunk44Norm x).property,(boundaryImPowerRow77_7Degree10Chunk48Norm x).property]

    dsimp only [boundaryImPowerRow77_7Degree10Chunk0Norm,boundaryImPowerRow77_7Degree10Chunk4Norm,boundaryImPowerRow77_7Degree10Chunk8Norm,boundaryImPowerRow77_7Degree10Chunk12Norm,boundaryImPowerRow77_7Degree10Chunk16Norm,boundaryImPowerRow77_7Degree10Chunk20Norm,boundaryImPowerRow77_7Degree10Chunk24Norm,boundaryImPowerRow77_7Degree10Chunk28Norm,boundaryImPowerRow77_7Degree10Chunk32Norm,boundaryImPowerRow77_7Degree10Chunk36Norm,boundaryImPowerRow77_7Degree10Chunk40Norm,boundaryImPowerRow77_7Degree10Chunk44Norm,boundaryImPowerRow77_7Degree10Chunk48Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((12527514121/2834352 : ℝ))/3) ((21-8)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((12527514121/2834352 : ℝ))/36) (((21-8)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((12527514121/2834352 : ℝ))/216) (((21-8)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((103937121884549/612220032 : ℝ))/3) ((21-8)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_8Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk0 x=boundaryImPowerRow77_8Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((103937121884549/612220032 : ℝ))/36) (((21-8)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((103937121884549/612220032 : ℝ))/216) (((21-8)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((22103980013276113/352638738432 : ℝ))/3) ((21-8)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((22103980013276113/352638738432 : ℝ))/36) (((21-8)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_8Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk4 x=boundaryImPowerRow77_8Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((22103980013276113/352638738432 : ℝ))/216) (((21-8)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-2764061372084054567/50779978334208 : ℝ))/3) ((21-8)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-2764061372084054567/50779978334208 : ℝ))/36) (((21-8)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-2764061372084054567/50779978334208 : ℝ))/216) (((21-8)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_8Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk8 x=boundaryImPowerRow77_8Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((112996085825195544631/7312316880125952 : ℝ))/3) ((21-8)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((112996085825195544631/7312316880125952 : ℝ))/36) (((21-8)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((112996085825195544631/7312316880125952 : ℝ))/216) (((21-8)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-1152414434751891020869/526486815369068544 : ℝ))/3) ((21-8)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_8Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk12 x=boundaryImPowerRow77_8Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-1152414434751891020869/526486815369068544 : ℝ))/36) (((21-8)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-1152414434751891020869/526486815369068544 : ℝ))/216) (((21-8)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((666591430340066365967/12635683568857645056 : ℝ))/3) ((21-8)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((666591430340066365967/12635683568857645056 : ℝ))/36) (((21-8)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_8Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk16 x=boundaryImPowerRow77_8Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((666591430340066365967/12635683568857645056 : ℝ))/216) (((21-8)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((40719454819020256086709/1364653825436625666048 : ℝ))/3) ((21-8)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((40719454819020256086709/1364653825436625666048 : ℝ))/36) (((21-8)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((40719454819020256086709/1364653825436625666048 : ℝ))/216) (((21-8)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_8Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk20 x=boundaryImPowerRow77_8Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-232348310570295420515159/49127537715718523977728 : ℝ))/3) ((21-8)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-232348310570295420515159/49127537715718523977728 : ℝ))/36) (((21-8)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-232348310570295420515159/49127537715718523977728 : ℝ))/216) (((21-8)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((25688294525482570044535/73691306573577785966592 : ℝ))/3) ((21-8)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_8Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk24 x=boundaryImPowerRow77_8Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((25688294525482570044535/73691306573577785966592 : ℝ))/36) (((21-8)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((25688294525482570044535/73691306573577785966592 : ℝ))/216) (((21-8)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((-116728468063016088656663/7958661109946400884391936 : ℝ))/3) ((21-8)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-116728468063016088656663/7958661109946400884391936 : ℝ))/36) (((21-8)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_8Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk28 x=boundaryImPowerRow77_8Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-116728468063016088656663/7958661109946400884391936 : ℝ))/216) (((21-8)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((2698262661898301017619/7958661109946400884391936 : ℝ))/3) ((21-8)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((2698262661898301017619/7958661109946400884391936 : ℝ))/36) (((21-8)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((2698262661898301017619/7958661109946400884391936 : ℝ))/216) (((21-8)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_8Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk32 x=boundaryImPowerRow77_8Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-667928938946074571671/214883849968552823878582272 : ℝ))/3) ((21-8)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-667928938946074571671/214883849968552823878582272 : ℝ))/36) (((21-8)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-667928938946074571671/214883849968552823878582272 : ℝ))/216) (((21-8)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((9061942056114367711/1933954649716975414907240448 : ℝ))/3) ((21-8)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_8Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk36 x=boundaryImPowerRow77_8Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((9061942056114367711/1933954649716975414907240448 : ℝ))/36) (((21-8)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((9061942056114367711/1933954649716975414907240448 : ℝ))/216) (((21-8)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((518578544687791259/26108387771179168101247746048 : ℝ))/3) ((21-8)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((518578544687791259/26108387771179168101247746048 : ℝ))/36) (((21-8)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_8Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk40 x=boundaryImPowerRow77_8Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((518578544687791259/26108387771179168101247746048 : ℝ))/216) (((21-8)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((-83858433492463/3671492030322070514237964288 : ℝ))/3) ((21-8)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((-83858433492463/3671492030322070514237964288 : ℝ))/36) (((21-8)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((-83858433492463/3671492030322070514237964288 : ℝ))/216) (((21-8)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_8Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk44 x=boundaryImPowerRow77_8Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((99107635249/88115808727729692341711142912 : ℝ))/3) ((21-8)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((99107635249/88115808727729692341711142912 : ℝ))/36) (((21-8)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((99107635249/88115808727729692341711142912 : ℝ))/216) (((21-8)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((-5764801/148695427228043855826637553664 : ℝ))/3) ((21-8)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_8Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk48 x=boundaryImPowerRow77_8Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((-5764801/148695427228043855826637553664 : ℝ))/36) (((21-8)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((-5764801/148695427228043855826637553664 : ℝ))/216) (((21-8)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_8Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_8Degree10Chunk52 x=boundaryImPowerRow77_8Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_8Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_8 10 x=c} := by

  have he : boundaryImPowerRow77_8 10 x=((((boundaryImPowerRow77_8Degree10Chunk0 x) + ((boundaryImPowerRow77_8Degree10Chunk4 x) + (boundaryImPowerRow77_8Degree10Chunk8 x))) + (((boundaryImPowerRow77_8Degree10Chunk12 x) + (boundaryImPowerRow77_8Degree10Chunk16 x)) + ((boundaryImPowerRow77_8Degree10Chunk20 x) + (boundaryImPowerRow77_8Degree10Chunk24 x)))) + (((boundaryImPowerRow77_8Degree10Chunk28 x) + ((boundaryImPowerRow77_8Degree10Chunk32 x) + (boundaryImPowerRow77_8Degree10Chunk36 x))) + (((boundaryImPowerRow77_8Degree10Chunk40 x) + (boundaryImPowerRow77_8Degree10Chunk44 x)) + ((boundaryImPowerRow77_8Degree10Chunk48 x) + (boundaryImPowerRow77_8Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_8,boundaryImPowerRow77_8Degree10Chunk0,boundaryImPowerRow77_8Degree10Chunk4,boundaryImPowerRow77_8Degree10Chunk8,boundaryImPowerRow77_8Degree10Chunk12,boundaryImPowerRow77_8Degree10Chunk16,boundaryImPowerRow77_8Degree10Chunk20,boundaryImPowerRow77_8Degree10Chunk24,boundaryImPowerRow77_8Degree10Chunk28,boundaryImPowerRow77_8Degree10Chunk32,boundaryImPowerRow77_8Degree10Chunk36,boundaryImPowerRow77_8Degree10Chunk40,boundaryImPowerRow77_8Degree10Chunk44,boundaryImPowerRow77_8Degree10Chunk48,boundaryImPowerRow77_8Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_8Degree10Chunk0Norm x).property,(boundaryImPowerRow77_8Degree10Chunk4Norm x).property,(boundaryImPowerRow77_8Degree10Chunk8Norm x).property,(boundaryImPowerRow77_8Degree10Chunk12Norm x).property,(boundaryImPowerRow77_8Degree10Chunk16Norm x).property,(boundaryImPowerRow77_8Degree10Chunk20Norm x).property,(boundaryImPowerRow77_8Degree10Chunk24Norm x).property,(boundaryImPowerRow77_8Degree10Chunk28Norm x).property,(boundaryImPowerRow77_8Degree10Chunk32Norm x).property,(boundaryImPowerRow77_8Degree10Chunk36Norm x).property,(boundaryImPowerRow77_8Degree10Chunk40Norm x).property,(boundaryImPowerRow77_8Degree10Chunk44Norm x).property,(boundaryImPowerRow77_8Degree10Chunk48Norm x).property,(boundaryImPowerRow77_8Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_8Degree10Chunk0Norm,boundaryImPowerRow77_8Degree10Chunk4Norm,boundaryImPowerRow77_8Degree10Chunk8Norm,boundaryImPowerRow77_8Degree10Chunk12Norm,boundaryImPowerRow77_8Degree10Chunk16Norm,boundaryImPowerRow77_8Degree10Chunk20Norm,boundaryImPowerRow77_8Degree10Chunk24Norm,boundaryImPowerRow77_8Degree10Chunk28Norm,boundaryImPowerRow77_8Degree10Chunk32Norm,boundaryImPowerRow77_8Degree10Chunk36Norm,boundaryImPowerRow77_8Degree10Chunk40Norm,boundaryImPowerRow77_8Degree10Chunk44Norm,boundaryImPowerRow77_8Degree10Chunk48Norm,boundaryImPowerRow77_8Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((883107573397/2125764 : ℝ))/3) ((21-9)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((883107573397/2125764 : ℝ))/36) (((21-9)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((883107573397/2125764 : ℝ))/216) (((21-9)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((33041956144873/51018336 : ℝ))/3) ((21-9)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_9Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk0 x=boundaryImPowerRow77_9Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((33041956144873/51018336 : ℝ))/36) (((21-9)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((33041956144873/51018336 : ℝ))/216) (((21-9)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-275023540930675933/705277476864 : ℝ))/3) ((21-9)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-275023540930675933/705277476864 : ℝ))/36) (((21-9)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_9Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk4 x=boundaryImPowerRow77_9Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-275023540930675933/705277476864 : ℝ))/216) (((21-9)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((4896217808561804567/50779978334208 : ℝ))/3) ((21-9)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((4896217808561804567/50779978334208 : ℝ))/36) (((21-9)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((4896217808561804567/50779978334208 : ℝ))/216) (((21-9)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_9Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk8 x=boundaryImPowerRow77_9Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-7877649846144796109/1218719480020992 : ℝ))/3) ((21-9)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-7877649846144796109/1218719480020992 : ℝ))/36) (((21-9)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-7877649846144796109/1218719480020992 : ℝ))/216) (((21-9)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-527453930303400479755/131621703842267136 : ℝ))/3) ((21-9)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_9Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk12 x=boundaryImPowerRow77_9Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-527453930303400479755/131621703842267136 : ℝ))/36) (((21-9)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-527453930303400479755/131621703842267136 : ℝ))/216) (((21-9)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((12458970774516295731425/9476762676643233792 : ℝ))/3) ((21-9)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((12458970774516295731425/9476762676643233792 : ℝ))/36) (((21-9)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_9Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk16 x=boundaryImPowerRow77_9Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((12458970774516295731425/9476762676643233792 : ℝ))/216) (((21-9)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-24349283258521101697/131621703842267136 : ℝ))/3) ((21-9)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-24349283258521101697/131621703842267136 : ℝ))/36) (((21-9)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-24349283258521101697/131621703842267136 : ℝ))/216) (((21-9)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_9Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk20 x=boundaryImPowerRow77_9Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((90695834307067983738521/6140942214464815497216 : ℝ))/3) ((21-9)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((90695834307067983738521/6140942214464815497216 : ℝ))/36) (((21-9)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((90695834307067983738521/6140942214464815497216 : ℝ))/216) (((21-9)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-109572784178532326192639/147382613147155571933184 : ℝ))/3) ((21-9)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_9Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk24 x=boundaryImPowerRow77_9Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-109572784178532326192639/147382613147155571933184 : ℝ))/36) (((21-9)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-109572784178532326192639/147382613147155571933184 : ℝ))/216) (((21-9)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((34450895411528530056647/1326443518324400147398656 : ℝ))/3) ((21-9)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((34450895411528530056647/1326443518324400147398656 : ℝ))/36) (((21-9)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_9Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk28 x=boundaryImPowerRow77_9Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((34450895411528530056647/1326443518324400147398656 : ℝ))/216) (((21-9)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-7912579175518822931677/11937991664919601326587904 : ℝ))/3) ((21-9)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-7912579175518822931677/11937991664919601326587904 : ℝ))/36) (((21-9)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-7912579175518822931677/11937991664919601326587904 : ℝ))/216) (((21-9)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_9Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk32 x=boundaryImPowerRow77_9Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((64669213170180283487/6715120311517275746205696 : ℝ))/3) ((21-9)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((64669213170180283487/6715120311517275746205696 : ℝ))/36) (((21-9)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((64669213170180283487/6715120311517275746205696 : ℝ))/216) (((21-9)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-50458074112147463491/966977324858487707453620224 : ℝ))/3) ((21-9)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_9Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk36 x=boundaryImPowerRow77_9Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-50458074112147463491/966977324858487707453620224 : ℝ))/36) (((21-9)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-50458074112147463491/966977324858487707453620224 : ℝ))/216) (((21-9)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((614700438185525405/8702795923726389367082582016 : ℝ))/3) ((21-9)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((614700438185525405/8702795923726389367082582016 : ℝ))/36) (((21-9)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_9Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk40 x=boundaryImPowerRow77_9Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((614700438185525405/8702795923726389367082582016 : ℝ))/216) (((21-9)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((311279414855647/78325163313537504303743238144 : ℝ))/3) ((21-9)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((311279414855647/78325163313537504303743238144 : ℝ))/36) (((21-9)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((311279414855647/78325163313537504303743238144 : ℝ))/216) (((21-9)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_9Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk44 x=boundaryImPowerRow77_9Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-1010051842051/176231617455459384683422285824 : ℝ))/3) ((21-9)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((-1010051842051/176231617455459384683422285824 : ℝ))/36) (((21-9)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((-1010051842051/176231617455459384683422285824 : ℝ))/216) (((21-9)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((-45294865/198260569637391807768850071552 : ℝ))/3) ((21-9)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_9Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk48 x=boundaryImPowerRow77_9Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((-45294865/198260569637391807768850071552 : ℝ))/36) (((21-9)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((-45294865/198260569637391807768850071552 : ℝ))/216) (((21-9)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_9Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_9Degree10Chunk52 x=boundaryImPowerRow77_9Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_9Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_9 10 x=c} := by

  have he : boundaryImPowerRow77_9 10 x=((((boundaryImPowerRow77_9Degree10Chunk0 x) + ((boundaryImPowerRow77_9Degree10Chunk4 x) + (boundaryImPowerRow77_9Degree10Chunk8 x))) + (((boundaryImPowerRow77_9Degree10Chunk12 x) + (boundaryImPowerRow77_9Degree10Chunk16 x)) + ((boundaryImPowerRow77_9Degree10Chunk20 x) + (boundaryImPowerRow77_9Degree10Chunk24 x)))) + (((boundaryImPowerRow77_9Degree10Chunk28 x) + ((boundaryImPowerRow77_9Degree10Chunk32 x) + (boundaryImPowerRow77_9Degree10Chunk36 x))) + (((boundaryImPowerRow77_9Degree10Chunk40 x) + (boundaryImPowerRow77_9Degree10Chunk44 x)) + ((boundaryImPowerRow77_9Degree10Chunk48 x) + (boundaryImPowerRow77_9Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_9,boundaryImPowerRow77_9Degree10Chunk0,boundaryImPowerRow77_9Degree10Chunk4,boundaryImPowerRow77_9Degree10Chunk8,boundaryImPowerRow77_9Degree10Chunk12,boundaryImPowerRow77_9Degree10Chunk16,boundaryImPowerRow77_9Degree10Chunk20,boundaryImPowerRow77_9Degree10Chunk24,boundaryImPowerRow77_9Degree10Chunk28,boundaryImPowerRow77_9Degree10Chunk32,boundaryImPowerRow77_9Degree10Chunk36,boundaryImPowerRow77_9Degree10Chunk40,boundaryImPowerRow77_9Degree10Chunk44,boundaryImPowerRow77_9Degree10Chunk48,boundaryImPowerRow77_9Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_9Degree10Chunk0Norm x).property,(boundaryImPowerRow77_9Degree10Chunk4Norm x).property,(boundaryImPowerRow77_9Degree10Chunk8Norm x).property,(boundaryImPowerRow77_9Degree10Chunk12Norm x).property,(boundaryImPowerRow77_9Degree10Chunk16Norm x).property,(boundaryImPowerRow77_9Degree10Chunk20Norm x).property,(boundaryImPowerRow77_9Degree10Chunk24Norm x).property,(boundaryImPowerRow77_9Degree10Chunk28Norm x).property,(boundaryImPowerRow77_9Degree10Chunk32Norm x).property,(boundaryImPowerRow77_9Degree10Chunk36Norm x).property,(boundaryImPowerRow77_9Degree10Chunk40Norm x).property,(boundaryImPowerRow77_9Degree10Chunk44Norm x).property,(boundaryImPowerRow77_9Degree10Chunk48Norm x).property,(boundaryImPowerRow77_9Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_9Degree10Chunk0Norm,boundaryImPowerRow77_9Degree10Chunk4Norm,boundaryImPowerRow77_9Degree10Chunk8Norm,boundaryImPowerRow77_9Degree10Chunk12Norm,boundaryImPowerRow77_9Degree10Chunk16Norm,boundaryImPowerRow77_9Degree10Chunk20Norm,boundaryImPowerRow77_9Degree10Chunk24Norm,boundaryImPowerRow77_9Degree10Chunk28Norm,boundaryImPowerRow77_9Degree10Chunk32Norm,boundaryImPowerRow77_9Degree10Chunk36Norm,boundaryImPowerRow77_9Degree10Chunk40Norm,boundaryImPowerRow77_9Degree10Chunk44Norm,boundaryImPowerRow77_9Degree10Chunk48Norm,boundaryImPowerRow77_9Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((1056981749179/531441 : ℝ))/3) ((21-10)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((1056981749179/531441 : ℝ))/36) (((21-10)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((1056981749179/531441 : ℝ))/216) (((21-10)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-11402695394645/12754584 : ℝ))/3) ((21-10)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_10Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk0 x=boundaryImPowerRow77_10Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-11402695394645/12754584 : ℝ))/36) (((21-10)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-11402695394645/12754584 : ℝ))/216) (((21-10)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((12870230893791391/470184984576 : ℝ))/3) ((21-10)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((12870230893791391/470184984576 : ℝ))/36) (((21-10)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_10Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk4 x=boundaryImPowerRow77_10Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((12870230893791391/470184984576 : ℝ))/216) (((21-10)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((7361937210697033783/50779978334208 : ℝ))/3) ((21-10)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((7361937210697033783/50779978334208 : ℝ))/36) (((21-10)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((7361937210697033783/50779978334208 : ℝ))/216) (((21-10)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_10Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk8 x=boundaryImPowerRow77_10Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-21005958712237110757/228509902503936 : ℝ))/3) ((21-10)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-21005958712237110757/228509902503936 : ℝ))/36) (((21-10)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-21005958712237110757/228509902503936 : ℝ))/216) (((21-10)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((277597856591286462035/10968475320188928 : ℝ))/3) ((21-10)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_10Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk12 x=boundaryImPowerRow77_10Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((277597856591286462035/10968475320188928 : ℝ))/36) (((21-10)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((277597856591286462035/10968475320188928 : ℝ))/216) (((21-10)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((-8689755945636813856739/2369190669160808448 : ℝ))/3) ((21-10)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-8689755945636813856739/2369190669160808448 : ℝ))/36) (((21-10)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_10Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk16 x=boundaryImPowerRow77_10Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-8689755945636813856739/2369190669160808448 : ℝ))/216) (((21-10)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((25228436644955969253769/85290864089789104128 : ℝ))/3) ((21-10)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((25228436644955969253769/85290864089789104128 : ℝ))/36) (((21-10)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((25228436644955969253769/85290864089789104128 : ℝ))/216) (((21-10)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_10Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk20 x=boundaryImPowerRow77_10Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-51781920294494115701321/4093961476309876998144 : ℝ))/3) ((21-10)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-51781920294494115701321/4093961476309876998144 : ℝ))/36) (((21-10)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-51781920294494115701321/4093961476309876998144 : ℝ))/216) (((21-10)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((22116772737772060641623/110536959860366678949888 : ℝ))/3) ((21-10)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_10Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk24 x=boundaryImPowerRow77_10Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((22116772737772060641623/110536959860366678949888 : ℝ))/36) (((21-10)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((22116772737772060641623/110536959860366678949888 : ℝ))/216) (((21-10)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((5381776536547254490367/1989665277486600221097984 : ℝ))/3) ((21-10)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((5381776536547254490367/1989665277486600221097984 : ℝ))/36) (((21-10)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_10Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk28 x=boundaryImPowerRow77_10Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((5381776536547254490367/1989665277486600221097984 : ℝ))/216) (((21-10)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-2461295950530559967/497416319371650055274496 : ℝ))/3) ((21-10)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-2461295950530559967/497416319371650055274496 : ℝ))/36) (((21-10)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-2461295950530559967/497416319371650055274496 : ℝ))/216) (((21-10)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_10Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk32 x=boundaryImPowerRow77_10Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-286583397345662596295/53720962492138205969645568 : ℝ))/3) ((21-10)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-286583397345662596295/53720962492138205969645568 : ℝ))/36) (((21-10)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-286583397345662596295/53720962492138205969645568 : ℝ))/216) (((21-10)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((35277275277781064663/483488662429243853726810112 : ℝ))/3) ((21-10)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_10Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk36 x=boundaryImPowerRow77_10Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((35277275277781064663/483488662429243853726810112 : ℝ))/36) (((21-10)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((35277275277781064663/483488662429243853726810112 : ℝ))/216) (((21-10)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((-3045337463733407/13430240623034551492411392 : ℝ))/3) ((21-10)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((-3045337463733407/13430240623034551492411392 : ℝ))/36) (((21-10)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_10Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk40 x=boundaryImPowerRow77_10Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-3045337463733407/13430240623034551492411392 : ℝ))/216) (((21-10)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((5692246506325295/39162581656768752151871619072 : ℝ))/3) ((21-10)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((5692246506325295/39162581656768752151871619072 : ℝ))/36) (((21-10)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((5692246506325295/39162581656768752151871619072 : ℝ))/216) (((21-10)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_10Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk44 x=boundaryImPowerRow77_10Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-43152392675/9790645414192188037967904768 : ℝ))/3) ((21-10)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((-43152392675/9790645414192188037967904768 : ℝ))/36) (((21-10)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((-43152392675/9790645414192188037967904768 : ℝ))/216) (((21-10)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((823543/5507238045483105771356946432 : ℝ))/3) ((21-10)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_10Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk48 x=boundaryImPowerRow77_10Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((823543/5507238045483105771356946432 : ℝ))/36) (((21-10)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((823543/5507238045483105771356946432 : ℝ))/216) (((21-10)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_10Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_10Degree10Chunk52 x=boundaryImPowerRow77_10Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_10Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_10Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_10 10 x=c} := by

  have he : boundaryImPowerRow77_10 10 x=((((boundaryImPowerRow77_10Degree10Chunk0 x) + ((boundaryImPowerRow77_10Degree10Chunk4 x) + (boundaryImPowerRow77_10Degree10Chunk8 x))) + (((boundaryImPowerRow77_10Degree10Chunk12 x) + (boundaryImPowerRow77_10Degree10Chunk16 x)) + ((boundaryImPowerRow77_10Degree10Chunk20 x) + (boundaryImPowerRow77_10Degree10Chunk24 x)))) + (((boundaryImPowerRow77_10Degree10Chunk28 x) + ((boundaryImPowerRow77_10Degree10Chunk32 x) + (boundaryImPowerRow77_10Degree10Chunk36 x))) + (((boundaryImPowerRow77_10Degree10Chunk40 x) + (boundaryImPowerRow77_10Degree10Chunk44 x)) + ((boundaryImPowerRow77_10Degree10Chunk48 x) + (boundaryImPowerRow77_10Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_10,boundaryImPowerRow77_10Degree10Chunk0,boundaryImPowerRow77_10Degree10Chunk4,boundaryImPowerRow77_10Degree10Chunk8,boundaryImPowerRow77_10Degree10Chunk12,boundaryImPowerRow77_10Degree10Chunk16,boundaryImPowerRow77_10Degree10Chunk20,boundaryImPowerRow77_10Degree10Chunk24,boundaryImPowerRow77_10Degree10Chunk28,boundaryImPowerRow77_10Degree10Chunk32,boundaryImPowerRow77_10Degree10Chunk36,boundaryImPowerRow77_10Degree10Chunk40,boundaryImPowerRow77_10Degree10Chunk44,boundaryImPowerRow77_10Degree10Chunk48,boundaryImPowerRow77_10Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_10Degree10Chunk0Norm x).property,(boundaryImPowerRow77_10Degree10Chunk4Norm x).property,(boundaryImPowerRow77_10Degree10Chunk8Norm x).property,(boundaryImPowerRow77_10Degree10Chunk12Norm x).property,(boundaryImPowerRow77_10Degree10Chunk16Norm x).property,(boundaryImPowerRow77_10Degree10Chunk20Norm x).property,(boundaryImPowerRow77_10Degree10Chunk24Norm x).property,(boundaryImPowerRow77_10Degree10Chunk28Norm x).property,(boundaryImPowerRow77_10Degree10Chunk32Norm x).property,(boundaryImPowerRow77_10Degree10Chunk36Norm x).property,(boundaryImPowerRow77_10Degree10Chunk40Norm x).property,(boundaryImPowerRow77_10Degree10Chunk44Norm x).property,(boundaryImPowerRow77_10Degree10Chunk48Norm x).property,(boundaryImPowerRow77_10Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_10Degree10Chunk0Norm,boundaryImPowerRow77_10Degree10Chunk4Norm,boundaryImPowerRow77_10Degree10Chunk8Norm,boundaryImPowerRow77_10Degree10Chunk12Norm,boundaryImPowerRow77_10Degree10Chunk16Norm,boundaryImPowerRow77_10Degree10Chunk20Norm,boundaryImPowerRow77_10Degree10Chunk24Norm,boundaryImPowerRow77_10Degree10Chunk28Norm,boundaryImPowerRow77_10Degree10Chunk32Norm,boundaryImPowerRow77_10Degree10Chunk36Norm,boundaryImPowerRow77_10Degree10Chunk40Norm,boundaryImPowerRow77_10Degree10Chunk44Norm,boundaryImPowerRow77_10Degree10Chunk48Norm,boundaryImPowerRow77_10Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((387862448546/531441 : ℝ))/3) ((21-11)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((387862448546/531441 : ℝ))/36) (((21-11)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((387862448546/531441 : ℝ))/216) (((21-11)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-1840027141589/1062882 : ℝ))/3) ((21-11)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_11Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk0 x=boundaryImPowerRow77_11Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-1840027141589/1062882 : ℝ))/36) (((21-11)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-1840027141589/1062882 : ℝ))/216) (((21-11)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((647159530264634513/470184984576 : ℝ))/3) ((21-11)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((647159530264634513/470184984576 : ℝ))/36) (((21-11)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_11Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk4 x=boundaryImPowerRow77_11Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((647159530264634513/470184984576 : ℝ))/216) (((21-11)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-6917532202939476529/8463329722368 : ℝ))/3) ((21-11)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-6917532202939476529/8463329722368 : ℝ))/36) (((21-11)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-6917532202939476529/8463329722368 : ℝ))/216) (((21-11)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_11Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk8 x=boundaryImPowerRow77_11Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((882016326540022631215/3656158440062976 : ℝ))/3) ((21-11)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((882016326540022631215/3656158440062976 : ℝ))/36) (((21-11)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((882016326540022631215/3656158440062976 : ℝ))/216) (((21-11)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-4545390810138934654915/131621703842267136 : ℝ))/3) ((21-11)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_11Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk12 x=boundaryImPowerRow77_11Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-4545390810138934654915/131621703842267136 : ℝ))/36) (((21-11)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-4545390810138934654915/131621703842267136 : ℝ))/216) (((21-11)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((1439110332312322964399/789730223053602816 : ℝ))/3) ((21-11)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((1439110332312322964399/789730223053602816 : ℝ))/36) (((21-11)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_11Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk16 x=boundaryImPowerRow77_11Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((1439110332312322964399/789730223053602816 : ℝ))/216) (((21-11)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((11486925271511345542985/85290864089789104128 : ℝ))/3) ((21-11)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((11486925271511345542985/85290864089789104128 : ℝ))/36) (((21-11)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((11486925271511345542985/85290864089789104128 : ℝ))/216) (((21-11)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_11Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk20 x=boundaryImPowerRow77_11Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-177667019376837771900037/6140942214464815497216 : ℝ))/3) ((21-11)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-177667019376837771900037/6140942214464815497216 : ℝ))/36) (((21-11)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-177667019376837771900037/6140942214464815497216 : ℝ))/216) (((21-11)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((30116181184398691347919/13817119982545834868736 : ℝ))/3) ((21-11)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_11Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk24 x=boundaryImPowerRow77_11Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((30116181184398691347919/13817119982545834868736 : ℝ))/36) (((21-11)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((30116181184398691347919/13817119982545834868736 : ℝ))/216) (((21-11)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((-11290153506474494427131/124354079842912513818624 : ℝ))/3) ((21-11)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-11290153506474494427131/124354079842912513818624 : ℝ))/36) (((21-11)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_11Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk28 x=boundaryImPowerRow77_11Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-11290153506474494427131/124354079842912513818624 : ℝ))/216) (((21-11)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((18890139867475262663467/8953493748689700994940928 : ℝ))/3) ((21-11)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((18890139867475262663467/8953493748689700994940928 : ℝ))/36) (((21-11)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((18890139867475262663467/8953493748689700994940928 : ℝ))/216) (((21-11)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_11Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk32 x=boundaryImPowerRow77_11Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-578781432778087876871/26860481246069102984822784 : ℝ))/3) ((21-11)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-578781432778087876871/26860481246069102984822784 : ℝ))/36) (((21-11)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-578781432778087876871/26860481246069102984822784 : ℝ))/216) (((21-11)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((70339605743459581/1259085058409489202413568 : ℝ))/3) ((21-11)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_11Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk36 x=boundaryImPowerRow77_11Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((70339605743459581/1259085058409489202413568 : ℝ))/36) (((21-11)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((70339605743459581/1259085058409489202413568 : ℝ))/216) (((21-11)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((100939973621334535/1087849490465798670885322752 : ℝ))/3) ((21-11)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((100939973621334535/1087849490465798670885322752 : ℝ))/36) (((21-11)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_11Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk40 x=boundaryImPowerRow77_11Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((100939973621334535/1087849490465798670885322752 : ℝ))/216) (((21-11)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((-1470496489030303/6527096942794792025311936512 : ℝ))/3) ((21-11)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((-1470496489030303/6527096942794792025311936512 : ℝ))/36) (((21-11)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((-1470496489030303/6527096942794792025311936512 : ℝ))/216) (((21-11)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_11Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk44 x=boundaryImPowerRow77_11Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((70124631227/2175698980931597341770645504 : ℝ))/3) ((21-11)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((70124631227/2175698980931597341770645504 : ℝ))/36) (((21-11)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((70124631227/2175698980931597341770645504 : ℝ))/216) (((21-11)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((24118045/11014476090966211542713892864 : ℝ))/3) ((21-11)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_11Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk48 x=boundaryImPowerRow77_11Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((24118045/11014476090966211542713892864 : ℝ))/36) (((21-11)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((24118045/11014476090966211542713892864 : ℝ))/216) (((21-11)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_11Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_11Degree10Chunk52 x=boundaryImPowerRow77_11Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_11Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_11 10 x=c} := by

  have he : boundaryImPowerRow77_11 10 x=((((boundaryImPowerRow77_11Degree10Chunk0 x) + ((boundaryImPowerRow77_11Degree10Chunk4 x) + (boundaryImPowerRow77_11Degree10Chunk8 x))) + (((boundaryImPowerRow77_11Degree10Chunk12 x) + (boundaryImPowerRow77_11Degree10Chunk16 x)) + ((boundaryImPowerRow77_11Degree10Chunk20 x) + (boundaryImPowerRow77_11Degree10Chunk24 x)))) + (((boundaryImPowerRow77_11Degree10Chunk28 x) + ((boundaryImPowerRow77_11Degree10Chunk32 x) + (boundaryImPowerRow77_11Degree10Chunk36 x))) + (((boundaryImPowerRow77_11Degree10Chunk40 x) + (boundaryImPowerRow77_11Degree10Chunk44 x)) + ((boundaryImPowerRow77_11Degree10Chunk48 x) + (boundaryImPowerRow77_11Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_11,boundaryImPowerRow77_11Degree10Chunk0,boundaryImPowerRow77_11Degree10Chunk4,boundaryImPowerRow77_11Degree10Chunk8,boundaryImPowerRow77_11Degree10Chunk12,boundaryImPowerRow77_11Degree10Chunk16,boundaryImPowerRow77_11Degree10Chunk20,boundaryImPowerRow77_11Degree10Chunk24,boundaryImPowerRow77_11Degree10Chunk28,boundaryImPowerRow77_11Degree10Chunk32,boundaryImPowerRow77_11Degree10Chunk36,boundaryImPowerRow77_11Degree10Chunk40,boundaryImPowerRow77_11Degree10Chunk44,boundaryImPowerRow77_11Degree10Chunk48,boundaryImPowerRow77_11Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_11Degree10Chunk0Norm x).property,(boundaryImPowerRow77_11Degree10Chunk4Norm x).property,(boundaryImPowerRow77_11Degree10Chunk8Norm x).property,(boundaryImPowerRow77_11Degree10Chunk12Norm x).property,(boundaryImPowerRow77_11Degree10Chunk16Norm x).property,(boundaryImPowerRow77_11Degree10Chunk20Norm x).property,(boundaryImPowerRow77_11Degree10Chunk24Norm x).property,(boundaryImPowerRow77_11Degree10Chunk28Norm x).property,(boundaryImPowerRow77_11Degree10Chunk32Norm x).property,(boundaryImPowerRow77_11Degree10Chunk36Norm x).property,(boundaryImPowerRow77_11Degree10Chunk40Norm x).property,(boundaryImPowerRow77_11Degree10Chunk44Norm x).property,(boundaryImPowerRow77_11Degree10Chunk48Norm x).property,(boundaryImPowerRow77_11Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_11Degree10Chunk0Norm,boundaryImPowerRow77_11Degree10Chunk4Norm,boundaryImPowerRow77_11Degree10Chunk8Norm,boundaryImPowerRow77_11Degree10Chunk12Norm,boundaryImPowerRow77_11Degree10Chunk16Norm,boundaryImPowerRow77_11Degree10Chunk20Norm,boundaryImPowerRow77_11Degree10Chunk24Norm,boundaryImPowerRow77_11Degree10Chunk28Norm,boundaryImPowerRow77_11Degree10Chunk32Norm,boundaryImPowerRow77_11Degree10Chunk36Norm,boundaryImPowerRow77_11Degree10Chunk40Norm,boundaryImPowerRow77_11Degree10Chunk44Norm,boundaryImPowerRow77_11Degree10Chunk48Norm,boundaryImPowerRow77_11Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-1986570578980/531441 : ℝ))/3) ((21-12)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-1986570578980/531441 : ℝ))/36) (((21-12)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-1986570578980/531441 : ℝ))/216) (((21-12)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((16747353386672/4782969 : ℝ))/3) ((21-12)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_12Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk0 x=boundaryImPowerRow77_12Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((16747353386672/4782969 : ℝ))/36) (((21-12)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((16747353386672/4782969 : ℝ))/216) (((21-12)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-2331474115948712719/705277476864 : ℝ))/3) ((21-12)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-2331474115948712719/705277476864 : ℝ))/36) (((21-12)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_12Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk4 x=boundaryImPowerRow77_12Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-2331474115948712719/705277476864 : ℝ))/216) (((21-12)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((6565504311987924541/6347497291776 : ℝ))/3) ((21-12)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((6565504311987924541/6347497291776 : ℝ))/36) (((21-12)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((6565504311987924541/6347497291776 : ℝ))/216) (((21-12)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_12Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk8 x=boundaryImPowerRow77_12Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-289008052064981183/4760622968832 : ℝ))/3) ((21-12)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-289008052064981183/4760622968832 : ℝ))/36) (((21-12)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-289008052064981183/4760622968832 : ℝ))/216) (((21-12)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-384738771558344262133/10968475320188928 : ℝ))/3) ((21-12)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_12Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk12 x=boundaryImPowerRow77_12Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-384738771558344262133/10968475320188928 : ℝ))/36) (((21-12)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-384738771558344262133/10968475320188928 : ℝ))/216) (((21-12)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((23806395026525945751893/2369190669160808448 : ℝ))/3) ((21-12)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((23806395026525945751893/2369190669160808448 : ℝ))/36) (((21-12)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_12Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk16 x=boundaryImPowerRow77_12Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((23806395026525945751893/2369190669160808448 : ℝ))/216) (((21-12)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-6416155732178433742061/4738381338321616896 : ℝ))/3) ((21-12)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-6416155732178433742061/4738381338321616896 : ℝ))/36) (((21-12)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-6416155732178433742061/4738381338321616896 : ℝ))/216) (((21-12)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_12Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk20 x=boundaryImPowerRow77_12Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((1797122151745559513509/15992037016835457024 : ℝ))/3) ((21-12)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((1797122151745559513509/15992037016835457024 : ℝ))/36) (((21-12)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((1797122151745559513509/15992037016835457024 : ℝ))/216) (((21-12)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-168832731406995898136789/27634239965091669737472 : ℝ))/3) ((21-12)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_12Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk24 x=boundaryImPowerRow77_12Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-168832731406995898136789/27634239965091669737472 : ℝ))/36) (((21-12)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-168832731406995898136789/27634239965091669737472 : ℝ))/216) (((21-12)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((1688705555747040690811/7772129990182032113664 : ℝ))/3) ((21-12)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((1688705555747040690811/7772129990182032113664 : ℝ))/36) (((21-12)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_12Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk28 x=boundaryImPowerRow77_12Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((1688705555747040690811/7772129990182032113664 : ℝ))/216) (((21-12)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-5438552691705840303863/1119186718586212624367616 : ℝ))/3) ((21-12)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-5438552691705840303863/1119186718586212624367616 : ℝ))/36) (((21-12)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-5438552691705840303863/1119186718586212624367616 : ℝ))/216) (((21-12)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_12Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk32 x=boundaryImPowerRow77_12Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((808998414497480038439/13430240623034551492411392 : ℝ))/3) ((21-12)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((808998414497480038439/13430240623034551492411392 : ℝ))/36) (((21-12)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((808998414497480038439/13430240623034551492411392 : ℝ))/216) (((21-12)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-6475796502468056641/20145360934551827238617088 : ℝ))/3) ((21-12)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_12Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk36 x=boundaryImPowerRow77_12Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-6475796502468056641/20145360934551827238617088 : ℝ))/36) (((21-12)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-6475796502468056641/20145360934551827238617088 : ℝ))/216) (((21-12)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((49987412050768249/90654124205483222573776896 : ℝ))/3) ((21-12)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((49987412050768249/90654124205483222573776896 : ℝ))/36) (((21-12)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_12Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk40 x=boundaryImPowerRow77_12Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((49987412050768249/90654124205483222573776896 : ℝ))/216) (((21-12)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((-5024567107355/33995296577056208465166336 : ℝ))/3) ((21-12)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((-5024567107355/33995296577056208465166336 : ℝ))/36) (((21-12)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((-5024567107355/33995296577056208465166336 : ℝ))/216) (((21-12)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_12Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk44 x=boundaryImPowerRow77_12Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-118522483457/3263548471397396012655968256 : ℝ))/3) ((21-12)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((-118522483457/3263548471397396012655968256 : ℝ))/36) (((21-12)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((-118522483457/3263548471397396012655968256 : ℝ))/216) (((21-12)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((-991613/917873007580517628559491072 : ℝ))/3) ((21-12)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_12Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk48 x=boundaryImPowerRow77_12Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((-991613/917873007580517628559491072 : ℝ))/36) (((21-12)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((-991613/917873007580517628559491072 : ℝ))/216) (((21-12)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_12Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_12Degree10Chunk52 x=boundaryImPowerRow77_12Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_12Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_12 10 x=c} := by

  have he : boundaryImPowerRow77_12 10 x=((((boundaryImPowerRow77_12Degree10Chunk0 x) + ((boundaryImPowerRow77_12Degree10Chunk4 x) + (boundaryImPowerRow77_12Degree10Chunk8 x))) + (((boundaryImPowerRow77_12Degree10Chunk12 x) + (boundaryImPowerRow77_12Degree10Chunk16 x)) + ((boundaryImPowerRow77_12Degree10Chunk20 x) + (boundaryImPowerRow77_12Degree10Chunk24 x)))) + (((boundaryImPowerRow77_12Degree10Chunk28 x) + ((boundaryImPowerRow77_12Degree10Chunk32 x) + (boundaryImPowerRow77_12Degree10Chunk36 x))) + (((boundaryImPowerRow77_12Degree10Chunk40 x) + (boundaryImPowerRow77_12Degree10Chunk44 x)) + ((boundaryImPowerRow77_12Degree10Chunk48 x) + (boundaryImPowerRow77_12Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_12,boundaryImPowerRow77_12Degree10Chunk0,boundaryImPowerRow77_12Degree10Chunk4,boundaryImPowerRow77_12Degree10Chunk8,boundaryImPowerRow77_12Degree10Chunk12,boundaryImPowerRow77_12Degree10Chunk16,boundaryImPowerRow77_12Degree10Chunk20,boundaryImPowerRow77_12Degree10Chunk24,boundaryImPowerRow77_12Degree10Chunk28,boundaryImPowerRow77_12Degree10Chunk32,boundaryImPowerRow77_12Degree10Chunk36,boundaryImPowerRow77_12Degree10Chunk40,boundaryImPowerRow77_12Degree10Chunk44,boundaryImPowerRow77_12Degree10Chunk48,boundaryImPowerRow77_12Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_12Degree10Chunk0Norm x).property,(boundaryImPowerRow77_12Degree10Chunk4Norm x).property,(boundaryImPowerRow77_12Degree10Chunk8Norm x).property,(boundaryImPowerRow77_12Degree10Chunk12Norm x).property,(boundaryImPowerRow77_12Degree10Chunk16Norm x).property,(boundaryImPowerRow77_12Degree10Chunk20Norm x).property,(boundaryImPowerRow77_12Degree10Chunk24Norm x).property,(boundaryImPowerRow77_12Degree10Chunk28Norm x).property,(boundaryImPowerRow77_12Degree10Chunk32Norm x).property,(boundaryImPowerRow77_12Degree10Chunk36Norm x).property,(boundaryImPowerRow77_12Degree10Chunk40Norm x).property,(boundaryImPowerRow77_12Degree10Chunk44Norm x).property,(boundaryImPowerRow77_12Degree10Chunk48Norm x).property,(boundaryImPowerRow77_12Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_12Degree10Chunk0Norm,boundaryImPowerRow77_12Degree10Chunk4Norm,boundaryImPowerRow77_12Degree10Chunk8Norm,boundaryImPowerRow77_12Degree10Chunk12Norm,boundaryImPowerRow77_12Degree10Chunk16Norm,boundaryImPowerRow77_12Degree10Chunk20Norm,boundaryImPowerRow77_12Degree10Chunk24Norm,boundaryImPowerRow77_12Degree10Chunk28Norm,boundaryImPowerRow77_12Degree10Chunk32Norm,boundaryImPowerRow77_12Degree10Chunk36Norm,boundaryImPowerRow77_12Degree10Chunk40Norm,boundaryImPowerRow77_12Degree10Chunk44Norm,boundaryImPowerRow77_12Degree10Chunk48Norm,boundaryImPowerRow77_12Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-21387348920/177147 : ℝ))/3) ((21-13)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-21387348920/177147 : ℝ))/36) (((21-13)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-21387348920/177147 : ℝ))/216) (((21-13)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-3394832635850/531441 : ℝ))/3) ((21-13)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_13Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk0 x=boundaryImPowerRow77_13Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-3394832635850/531441 : ℝ))/36) (((21-13)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-3394832635850/531441 : ℝ))/216) (((21-13)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((33228267578653235/39182082048 : ℝ))/3) ((21-13)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((33228267578653235/39182082048 : ℝ))/36) (((21-13)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_13Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk4 x=boundaryImPowerRow77_13Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((33228267578653235/39182082048 : ℝ))/216) (((21-13)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((4339944743525504705/3173748645888 : ℝ))/3) ((21-13)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((4339944743525504705/3173748645888 : ℝ))/36) (((21-13)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((4339944743525504705/3173748645888 : ℝ))/216) (((21-13)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_13Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk8 x=boundaryImPowerRow77_13Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-162875512255664436413/228509902503936 : ℝ))/3) ((21-13)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-162875512255664436413/228509902503936 : ℝ))/36) (((21-13)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-162875512255664436413/228509902503936 : ℝ))/216) (((21-13)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((4431864761983718933/25389989167104 : ℝ))/3) ((21-13)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_13Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk12 x=boundaryImPowerRow77_13Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((4431864761983718933/25389989167104 : ℝ))/36) (((21-13)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((4431864761983718933/25389989167104 : ℝ))/216) (((21-13)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((-31719383994419434377493/1184595334580404224 : ℝ))/3) ((21-13)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-31719383994419434377493/1184595334580404224 : ℝ))/36) (((21-13)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_13Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk16 x=boundaryImPowerRow77_13Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-31719383994419434377493/1184595334580404224 : ℝ))/216) (((21-13)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((60167119326862619049737/21322716022447276032 : ℝ))/3) ((21-13)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((60167119326862619049737/21322716022447276032 : ℝ))/36) (((21-13)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((60167119326862619049737/21322716022447276032 : ℝ))/216) (((21-13)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_13Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk20 x=boundaryImPowerRow77_13Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-53454047900078358757529/255872592269367312384 : ℝ))/3) ((21-13)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-53454047900078358757529/255872592269367312384 : ℝ))/36) (((21-13)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-53454047900078358757529/255872592269367312384 : ℝ))/216) (((21-13)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((146598159183810982851329/13817119982545834868736 : ℝ))/3) ((21-13)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_13Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk24 x=boundaryImPowerRow77_13Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((146598159183810982851329/13817119982545834868736 : ℝ))/36) (((21-13)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((146598159183810982851329/13817119982545834868736 : ℝ))/216) (((21-13)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((-10918644408274193254457/31088519960728128454656 : ℝ))/3) ((21-13)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-10918644408274193254457/31088519960728128454656 : ℝ))/36) (((21-13)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_13Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk28 x=boundaryImPowerRow77_13Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-10918644408274193254457/31088519960728128454656 : ℝ))/216) (((21-13)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((2678650914043232871421/373062239528737541455872 : ℝ))/3) ((21-13)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((2678650914043232871421/373062239528737541455872 : ℝ))/36) (((21-13)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((2678650914043232871421/373062239528737541455872 : ℝ))/216) (((21-13)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_13Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk32 x=boundaryImPowerRow77_13Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-217482139099894383509/2518170116818978404827136 : ℝ))/3) ((21-13)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-217482139099894383509/2518170116818978404827136 : ℝ))/36) (((21-13)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-217482139099894383509/2518170116818978404827136 : ℝ))/216) (((21-13)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((582702428059627343/1119186718586212624367616 : ℝ))/3) ((21-13)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_13Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk36 x=boundaryImPowerRow77_13Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((582702428059627343/1119186718586212624367616 : ℝ))/36) (((21-13)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((582702428059627343/1119186718586212624367616 : ℝ))/216) (((21-13)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((-2067650774550053/1678780077879318936551424 : ℝ))/3) ((21-13)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((-2067650774550053/1678780077879318936551424 : ℝ))/36) (((21-13)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_13Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk40 x=boundaryImPowerRow77_13Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-2067650774550053/1678780077879318936551424 : ℝ))/216) (((21-13)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((1533163870865/1888627587614233803620352 : ℝ))/3) ((21-13)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((1533163870865/1888627587614233803620352 : ℝ))/36) (((21-13)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((1533163870865/1888627587614233803620352 : ℝ))/216) (((21-13)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_13Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk44 x=boundaryImPowerRow77_13Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-59507903/3777255175228467607240704 : ℝ))/3) ((21-13)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((-59507903/3777255175228467607240704 : ℝ))/36) (((21-13)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((-59507903/3777255175228467607240704 : ℝ))/216) (((21-13)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((-2518649/271962372616449667721330688 : ℝ))/3) ((21-13)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_13Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk48 x=boundaryImPowerRow77_13Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((-2518649/271962372616449667721330688 : ℝ))/36) (((21-13)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((-2518649/271962372616449667721330688 : ℝ))/216) (((21-13)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_13Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_13Degree10Chunk52 x=boundaryImPowerRow77_13Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_13Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_13Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_13 10 x=c} := by

  have he : boundaryImPowerRow77_13 10 x=((((boundaryImPowerRow77_13Degree10Chunk0 x) + ((boundaryImPowerRow77_13Degree10Chunk4 x) + (boundaryImPowerRow77_13Degree10Chunk8 x))) + (((boundaryImPowerRow77_13Degree10Chunk12 x) + (boundaryImPowerRow77_13Degree10Chunk16 x)) + ((boundaryImPowerRow77_13Degree10Chunk20 x) + (boundaryImPowerRow77_13Degree10Chunk24 x)))) + (((boundaryImPowerRow77_13Degree10Chunk28 x) + ((boundaryImPowerRow77_13Degree10Chunk32 x) + (boundaryImPowerRow77_13Degree10Chunk36 x))) + (((boundaryImPowerRow77_13Degree10Chunk40 x) + (boundaryImPowerRow77_13Degree10Chunk44 x)) + ((boundaryImPowerRow77_13Degree10Chunk48 x) + (boundaryImPowerRow77_13Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_13,boundaryImPowerRow77_13Degree10Chunk0,boundaryImPowerRow77_13Degree10Chunk4,boundaryImPowerRow77_13Degree10Chunk8,boundaryImPowerRow77_13Degree10Chunk12,boundaryImPowerRow77_13Degree10Chunk16,boundaryImPowerRow77_13Degree10Chunk20,boundaryImPowerRow77_13Degree10Chunk24,boundaryImPowerRow77_13Degree10Chunk28,boundaryImPowerRow77_13Degree10Chunk32,boundaryImPowerRow77_13Degree10Chunk36,boundaryImPowerRow77_13Degree10Chunk40,boundaryImPowerRow77_13Degree10Chunk44,boundaryImPowerRow77_13Degree10Chunk48,boundaryImPowerRow77_13Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_13Degree10Chunk0Norm x).property,(boundaryImPowerRow77_13Degree10Chunk4Norm x).property,(boundaryImPowerRow77_13Degree10Chunk8Norm x).property,(boundaryImPowerRow77_13Degree10Chunk12Norm x).property,(boundaryImPowerRow77_13Degree10Chunk16Norm x).property,(boundaryImPowerRow77_13Degree10Chunk20Norm x).property,(boundaryImPowerRow77_13Degree10Chunk24Norm x).property,(boundaryImPowerRow77_13Degree10Chunk28Norm x).property,(boundaryImPowerRow77_13Degree10Chunk32Norm x).property,(boundaryImPowerRow77_13Degree10Chunk36Norm x).property,(boundaryImPowerRow77_13Degree10Chunk40Norm x).property,(boundaryImPowerRow77_13Degree10Chunk44Norm x).property,(boundaryImPowerRow77_13Degree10Chunk48Norm x).property,(boundaryImPowerRow77_13Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_13Degree10Chunk0Norm,boundaryImPowerRow77_13Degree10Chunk4Norm,boundaryImPowerRow77_13Degree10Chunk8Norm,boundaryImPowerRow77_13Degree10Chunk12Norm,boundaryImPowerRow77_13Degree10Chunk16Norm,boundaryImPowerRow77_13Degree10Chunk20Norm,boundaryImPowerRow77_13Degree10Chunk24Norm,boundaryImPowerRow77_13Degree10Chunk28Norm,boundaryImPowerRow77_13Degree10Chunk32Norm,boundaryImPowerRow77_13Degree10Chunk36Norm,boundaryImPowerRow77_13Degree10Chunk40Norm,boundaryImPowerRow77_13Degree10Chunk44Norm,boundaryImPowerRow77_13Degree10Chunk48Norm,boundaryImPowerRow77_13Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-5134963891520/531441 : ℝ))/3) ((21-14)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-5134963891520/531441 : ℝ))/36) (((21-14)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-5134963891520/531441 : ℝ))/216) (((21-14)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-35095739829088/4782969 : ℝ))/3) ((21-14)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_14Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk0 x=boundaryImPowerRow77_14Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-35095739829088/4782969 : ℝ))/36) (((21-14)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-35095739829088/4782969 : ℝ))/216) (((21-14)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((604606809589446209/58773123072 : ℝ))/3) ((21-14)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((604606809589446209/58773123072 : ℝ))/36) (((21-14)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_14Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk4 x=boundaryImPowerRow77_14Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((604606809589446209/58773123072 : ℝ))/216) (((21-14)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-7754220762129884119/1586874322944 : ℝ))/3) ((21-14)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-7754220762129884119/1586874322944 : ℝ))/36) (((21-14)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-7754220762129884119/1586874322944 : ℝ))/216) (((21-14)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_14Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk8 x=boundaryImPowerRow77_14Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((77952780941915794805/57127475625984 : ℝ))/3) ((21-14)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((77952780941915794805/57127475625984 : ℝ))/36) (((21-14)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((77952780941915794805/57127475625984 : ℝ))/216) (((21-14)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-2142573310515031248481/8226356490141696 : ℝ))/3) ((21-14)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_14Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk12 x=boundaryImPowerRow77_14Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-2142573310515031248481/8226356490141696 : ℝ))/36) (((21-14)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-2142573310515031248481/8226356490141696 : ℝ))/216) (((21-14)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((21476636981648276397217/592297667290202112 : ℝ))/3) ((21-14)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((21476636981648276397217/592297667290202112 : ℝ))/36) (((21-14)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_14Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk16 x=boundaryImPowerRow77_14Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((21476636981648276397217/592297667290202112 : ℝ))/216) (((21-14)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-39705129638856741393889/10661358011223638016 : ℝ))/3) ((21-14)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-39705129638856741393889/10661358011223638016 : ℝ))/36) (((21-14)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-39705129638856741393889/10661358011223638016 : ℝ))/216) (((21-14)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_14Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk20 x=boundaryImPowerRow77_14Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((26276211601461844624817/95952222101012742144 : ℝ))/3) ((21-14)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((26276211601461844624817/95952222101012742144 : ℝ))/36) (((21-14)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((26276211601461844624817/95952222101012742144 : ℝ))/216) (((21-14)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-94151306940429308087569/6908559991272917434368 : ℝ))/3) ((21-14)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_14Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk24 x=boundaryImPowerRow77_14Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-94151306940429308087569/6908559991272917434368 : ℝ))/36) (((21-14)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-94151306940429308087569/6908559991272917434368 : ℝ))/216) (((21-14)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((8857539250109601020951/20725679973818752303104 : ℝ))/3) ((21-14)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((8857539250109601020951/20725679973818752303104 : ℝ))/36) (((21-14)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_14Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk28 x=boundaryImPowerRow77_14Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((8857539250109601020951/20725679973818752303104 : ℝ))/216) (((21-14)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-1099298370620383148009/139898339823276578045952 : ℝ))/3) ((21-14)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-1099298370620383148009/139898339823276578045952 : ℝ))/36) (((21-14)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-1099298370620383148009/139898339823276578045952 : ℝ))/216) (((21-14)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_14Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk32 x=boundaryImPowerRow77_14Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((139479190140860759029/1678780077879318936551424 : ℝ))/3) ((21-14)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((139479190140860759029/1678780077879318936551424 : ℝ))/36) (((21-14)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((139479190140860759029/1678780077879318936551424 : ℝ))/216) (((21-14)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-90558618457966681/186531119764368770727936 : ℝ))/3) ((21-14)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_14Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk36 x=boundaryImPowerRow77_14Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-90558618457966681/186531119764368770727936 : ℝ))/36) (((21-14)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-90558618457966681/186531119764368770727936 : ℝ))/216) (((21-14)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((542692285773281/419695019469829734137856 : ℝ))/3) ((21-14)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((542692285773281/419695019469829734137856 : ℝ))/36) (((21-14)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_14Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk40 x=boundaryImPowerRow77_14Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((542692285773281/419695019469829734137856 : ℝ))/216) (((21-14)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((-2875535311745/2518170116818978404827136 : ℝ))/3) ((21-14)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((-2875535311745/2518170116818978404827136 : ℝ))/36) (((21-14)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((-2875535311745/2518170116818978404827136 : ℝ))/216) (((21-14)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_14Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk44 x=boundaryImPowerRow77_14Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((381175765/2518170116818978404827136 : ℝ))/3) ((21-14)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((381175765/2518170116818978404827136 : ℝ))/36) (((21-14)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((381175765/2518170116818978404827136 : ℝ))/216) (((21-14)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((171157/16997648288528104232583168 : ℝ))/3) ((21-14)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_14Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk48 x=boundaryImPowerRow77_14Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((171157/16997648288528104232583168 : ℝ))/36) (((21-14)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((171157/16997648288528104232583168 : ℝ))/216) (((21-14)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_14Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_14Degree10Chunk52 x=boundaryImPowerRow77_14Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_14Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_14 10 x=c} := by

  have he : boundaryImPowerRow77_14 10 x=((((boundaryImPowerRow77_14Degree10Chunk0 x) + ((boundaryImPowerRow77_14Degree10Chunk4 x) + (boundaryImPowerRow77_14Degree10Chunk8 x))) + (((boundaryImPowerRow77_14Degree10Chunk12 x) + (boundaryImPowerRow77_14Degree10Chunk16 x)) + ((boundaryImPowerRow77_14Degree10Chunk20 x) + (boundaryImPowerRow77_14Degree10Chunk24 x)))) + (((boundaryImPowerRow77_14Degree10Chunk28 x) + ((boundaryImPowerRow77_14Degree10Chunk32 x) + (boundaryImPowerRow77_14Degree10Chunk36 x))) + (((boundaryImPowerRow77_14Degree10Chunk40 x) + (boundaryImPowerRow77_14Degree10Chunk44 x)) + ((boundaryImPowerRow77_14Degree10Chunk48 x) + (boundaryImPowerRow77_14Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_14,boundaryImPowerRow77_14Degree10Chunk0,boundaryImPowerRow77_14Degree10Chunk4,boundaryImPowerRow77_14Degree10Chunk8,boundaryImPowerRow77_14Degree10Chunk12,boundaryImPowerRow77_14Degree10Chunk16,boundaryImPowerRow77_14Degree10Chunk20,boundaryImPowerRow77_14Degree10Chunk24,boundaryImPowerRow77_14Degree10Chunk28,boundaryImPowerRow77_14Degree10Chunk32,boundaryImPowerRow77_14Degree10Chunk36,boundaryImPowerRow77_14Degree10Chunk40,boundaryImPowerRow77_14Degree10Chunk44,boundaryImPowerRow77_14Degree10Chunk48,boundaryImPowerRow77_14Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_14Degree10Chunk0Norm x).property,(boundaryImPowerRow77_14Degree10Chunk4Norm x).property,(boundaryImPowerRow77_14Degree10Chunk8Norm x).property,(boundaryImPowerRow77_14Degree10Chunk12Norm x).property,(boundaryImPowerRow77_14Degree10Chunk16Norm x).property,(boundaryImPowerRow77_14Degree10Chunk20Norm x).property,(boundaryImPowerRow77_14Degree10Chunk24Norm x).property,(boundaryImPowerRow77_14Degree10Chunk28Norm x).property,(boundaryImPowerRow77_14Degree10Chunk32Norm x).property,(boundaryImPowerRow77_14Degree10Chunk36Norm x).property,(boundaryImPowerRow77_14Degree10Chunk40Norm x).property,(boundaryImPowerRow77_14Degree10Chunk44Norm x).property,(boundaryImPowerRow77_14Degree10Chunk48Norm x).property,(boundaryImPowerRow77_14Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_14Degree10Chunk0Norm,boundaryImPowerRow77_14Degree10Chunk4Norm,boundaryImPowerRow77_14Degree10Chunk8Norm,boundaryImPowerRow77_14Degree10Chunk12Norm,boundaryImPowerRow77_14Degree10Chunk16Norm,boundaryImPowerRow77_14Degree10Chunk20Norm,boundaryImPowerRow77_14Degree10Chunk24Norm,boundaryImPowerRow77_14Degree10Chunk28Norm,boundaryImPowerRow77_14Degree10Chunk32Norm,boundaryImPowerRow77_14Degree10Chunk36Norm,boundaryImPowerRow77_14Degree10Chunk40Norm,boundaryImPowerRow77_14Degree10Chunk44Norm,boundaryImPowerRow77_14Degree10Chunk48Norm,boundaryImPowerRow77_14Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-13348111443328/531441 : ℝ))/3) ((21-15)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((-13348111443328/531441 : ℝ))/36) (((21-15)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((-13348111443328/531441 : ℝ))/216) (((21-15)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((121624395483872/4782969 : ℝ))/3) ((21-15)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_15Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk0 x=boundaryImPowerRow77_15Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((121624395483872/4782969 : ℝ))/36) (((21-15)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((121624395483872/4782969 : ℝ))/216) (((21-15)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((-1217373131793371045/88159684608 : ℝ))/3) ((21-15)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-1217373131793371045/88159684608 : ℝ))/36) (((21-15)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_15Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk4 x=boundaryImPowerRow77_15Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-1217373131793371045/88159684608 : ℝ))/216) (((21-15)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((1952289368708571257/396718580736 : ℝ))/3) ((21-15)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((1952289368708571257/396718580736 : ℝ))/36) (((21-15)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((1952289368708571257/396718580736 : ℝ))/216) (((21-15)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_15Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk8 x=boundaryImPowerRow77_15Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-142384554437803330775/114254951251968 : ℝ))/3) ((21-15)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-142384554437803330775/114254951251968 : ℝ))/36) (((21-15)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((-142384554437803330775/114254951251968 : ℝ))/216) (((21-15)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((967959029416596061405/4113178245070848 : ℝ))/3) ((21-15)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_15Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk12 x=boundaryImPowerRow77_15Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((967959029416596061405/4113178245070848 : ℝ))/36) (((21-15)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((967959029416596061405/4113178245070848 : ℝ))/216) (((21-15)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((-9913731652170419685223/296148833645101056 : ℝ))/3) ((21-15)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-9913731652170419685223/296148833645101056 : ℝ))/36) (((21-15)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_15Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk16 x=boundaryImPowerRow77_15Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-9913731652170419685223/296148833645101056 : ℝ))/216) (((21-15)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((37298378120628914810429/10661358011223638016 : ℝ))/3) ((21-15)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((37298378120628914810429/10661358011223638016 : ℝ))/36) (((21-15)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((37298378120628914810429/10661358011223638016 : ℝ))/216) (((21-15)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_15Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk20 x=boundaryImPowerRow77_15Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-49254447986530343382971/191904444202025484288 : ℝ))/3) ((21-15)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-49254447986530343382971/191904444202025484288 : ℝ))/36) (((21-15)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((-49254447986530343382971/191904444202025484288 : ℝ))/216) (((21-15)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((9566163794288972646301/767617776808101937152 : ℝ))/3) ((21-15)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_15Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk24 x=boundaryImPowerRow77_15Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((9566163794288972646301/767617776808101937152 : ℝ))/36) (((21-15)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((9566163794288972646301/767617776808101937152 : ℝ))/216) (((21-15)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((-40034513487506580839/107946249863639334912 : ℝ))/3) ((21-15)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-40034513487506580839/107946249863639334912 : ℝ))/36) (((21-15)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_15Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk28 x=boundaryImPowerRow77_15Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-40034513487506580839/107946249863639334912 : ℝ))/216) (((21-15)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((573156975769303689767/93265559882184385363968 : ℝ))/3) ((21-15)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((573156975769303689767/93265559882184385363968 : ℝ))/36) (((21-15)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((573156975769303689767/93265559882184385363968 : ℝ))/216) (((21-15)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_15Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk32 x=boundaryImPowerRow77_15Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-472692161127254209/8743646238954786127872 : ℝ))/3) ((21-15)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-472692161127254209/8743646238954786127872 : ℝ))/36) (((21-15)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((-472692161127254209/8743646238954786127872 : ℝ))/216) (((21-15)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((5624931260846731/20725679973818752303104 : ℝ))/3) ((21-15)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_15Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk36 x=boundaryImPowerRow77_15Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((5624931260846731/20725679973818752303104 : ℝ))/36) (((21-15)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((5624931260846731/20725679973818752303104 : ℝ))/216) (((21-15)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((-213556033693019/279796679646553156091904 : ℝ))/3) ((21-15)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((-213556033693019/279796679646553156091904 : ℝ))/36) (((21-15)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_15Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk40 x=boundaryImPowerRow77_15Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-213556033693019/279796679646553156091904 : ℝ))/216) (((21-15)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((390571534915/419695019469829734137856 : ℝ))/3) ((21-15)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((390571534915/419695019469829734137856 : ℝ))/36) (((21-15)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((390571534915/419695019469829734137856 : ℝ))/216) (((21-15)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_15Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk44 x=boundaryImPowerRow77_15Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-839312737/2518170116818978404827136 : ℝ))/3) ((21-15)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((-839312737/2518170116818978404827136 : ℝ))/36) (((21-15)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((-839312737/2518170116818978404827136 : ℝ))/216) (((21-15)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((75943/5665882762842701410861056 : ℝ))/3) ((21-15)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_15Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk48 x=boundaryImPowerRow77_15Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((75943/5665882762842701410861056 : ℝ))/36) (((21-15)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((75943/5665882762842701410861056 : ℝ))/216) (((21-15)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_15Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_15Degree10Chunk52 x=boundaryImPowerRow77_15Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_15Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_15 10 x=c} := by

  have he : boundaryImPowerRow77_15 10 x=((((boundaryImPowerRow77_15Degree10Chunk0 x) + ((boundaryImPowerRow77_15Degree10Chunk4 x) + (boundaryImPowerRow77_15Degree10Chunk8 x))) + (((boundaryImPowerRow77_15Degree10Chunk12 x) + (boundaryImPowerRow77_15Degree10Chunk16 x)) + ((boundaryImPowerRow77_15Degree10Chunk20 x) + (boundaryImPowerRow77_15Degree10Chunk24 x)))) + (((boundaryImPowerRow77_15Degree10Chunk28 x) + ((boundaryImPowerRow77_15Degree10Chunk32 x) + (boundaryImPowerRow77_15Degree10Chunk36 x))) + (((boundaryImPowerRow77_15Degree10Chunk40 x) + (boundaryImPowerRow77_15Degree10Chunk44 x)) + ((boundaryImPowerRow77_15Degree10Chunk48 x) + (boundaryImPowerRow77_15Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_15,boundaryImPowerRow77_15Degree10Chunk0,boundaryImPowerRow77_15Degree10Chunk4,boundaryImPowerRow77_15Degree10Chunk8,boundaryImPowerRow77_15Degree10Chunk12,boundaryImPowerRow77_15Degree10Chunk16,boundaryImPowerRow77_15Degree10Chunk20,boundaryImPowerRow77_15Degree10Chunk24,boundaryImPowerRow77_15Degree10Chunk28,boundaryImPowerRow77_15Degree10Chunk32,boundaryImPowerRow77_15Degree10Chunk36,boundaryImPowerRow77_15Degree10Chunk40,boundaryImPowerRow77_15Degree10Chunk44,boundaryImPowerRow77_15Degree10Chunk48,boundaryImPowerRow77_15Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_15Degree10Chunk0Norm x).property,(boundaryImPowerRow77_15Degree10Chunk4Norm x).property,(boundaryImPowerRow77_15Degree10Chunk8Norm x).property,(boundaryImPowerRow77_15Degree10Chunk12Norm x).property,(boundaryImPowerRow77_15Degree10Chunk16Norm x).property,(boundaryImPowerRow77_15Degree10Chunk20Norm x).property,(boundaryImPowerRow77_15Degree10Chunk24Norm x).property,(boundaryImPowerRow77_15Degree10Chunk28Norm x).property,(boundaryImPowerRow77_15Degree10Chunk32Norm x).property,(boundaryImPowerRow77_15Degree10Chunk36Norm x).property,(boundaryImPowerRow77_15Degree10Chunk40Norm x).property,(boundaryImPowerRow77_15Degree10Chunk44Norm x).property,(boundaryImPowerRow77_15Degree10Chunk48Norm x).property,(boundaryImPowerRow77_15Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_15Degree10Chunk0Norm,boundaryImPowerRow77_15Degree10Chunk4Norm,boundaryImPowerRow77_15Degree10Chunk8Norm,boundaryImPowerRow77_15Degree10Chunk12Norm,boundaryImPowerRow77_15Degree10Chunk16Norm,boundaryImPowerRow77_15Degree10Chunk20Norm,boundaryImPowerRow77_15Degree10Chunk24Norm,boundaryImPowerRow77_15Degree10Chunk28Norm,boundaryImPowerRow77_15Degree10Chunk32Norm,boundaryImPowerRow77_15Degree10Chunk36Norm,boundaryImPowerRow77_15Degree10Chunk40Norm,boundaryImPowerRow77_15Degree10Chunk44Norm,boundaryImPowerRow77_15Degree10Chunk48Norm,boundaryImPowerRow77_15Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((2528462995456/531441 : ℝ))/3) ((21-16)+2*0-5) 0 0 10 x) + (boundaryTermPowerRow77 (-((2528462995456/531441 : ℝ))/36) (((21-16)+2*0-5)+1) 1 0 10 x)) + ((boundaryTermPowerRow77 (7*((2528462995456/531441 : ℝ))/216) (((21-16)+2*0-5)+2) 1 0 10 x) + (boundaryTermPowerRow77 (((-17099871361024/1594323 : ℝ))/3) ((21-16)+2*1-5) 0 1 10 x)))

def boundaryImPowerRow77_16Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk0 x=boundaryImPowerRow77_16Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-17099871361024/1594323 : ℝ))/36) (((21-16)+2*1-5)+1) 1 1 10 x) + (boundaryTermPowerRow77 (7*((-17099871361024/1594323 : ℝ))/216) (((21-16)+2*1-5)+2) 1 1 10 x)) + ((boundaryTermPowerRow77 (((109574406966704513/14693280768 : ℝ))/3) ((21-16)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((109574406966704513/14693280768 : ℝ))/36) (((21-16)+2*2-5)+1) 1 2 10 x)))

def boundaryImPowerRow77_16Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk4 x=boundaryImPowerRow77_16Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((109574406966704513/14693280768 : ℝ))/216) (((21-16)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-375791054218986221/132239526912 : ℝ))/3) ((21-16)+2*3-5) 0 3 10 x)) + ((boundaryTermPowerRow77 (-((-375791054218986221/132239526912 : ℝ))/36) (((21-16)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-375791054218986221/132239526912 : ℝ))/216) (((21-16)+2*3-5)+2) 1 3 10 x)))

def boundaryImPowerRow77_16Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk8 x=boundaryImPowerRow77_16Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((7018160380710446653/9521245937664 : ℝ))/3) ((21-16)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((7018160380710446653/9521245937664 : ℝ))/36) (((21-16)+2*4-5)+1) 1 4 10 x)) + ((boundaryTermPowerRow77 (7*((7018160380710446653/9521245937664 : ℝ))/216) (((21-16)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-12218341762226909015/85691213438976 : ℝ))/3) ((21-16)+2*5-5) 0 5 10 x)))

def boundaryImPowerRow77_16Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk12 x=boundaryImPowerRow77_16Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-12218341762226909015/85691213438976 : ℝ))/36) (((21-16)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-12218341762226909015/85691213438976 : ℝ))/216) (((21-16)+2*5-5)+2) 1 5 10 x)) + ((boundaryTermPowerRow77 (((170844576349099210283/8226356490141696 : ℝ))/3) ((21-16)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((170844576349099210283/8226356490141696 : ℝ))/36) (((21-16)+2*6-5)+1) 1 6 10 x)))

def boundaryImPowerRow77_16Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk16 x=boundaryImPowerRow77_16Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((170844576349099210283/8226356490141696 : ℝ))/216) (((21-16)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-3909468748870903135145/1776893001870606336 : ℝ))/3) ((21-16)+2*7-5) 0 7 10 x)) + ((boundaryTermPowerRow77 (-((-3909468748870903135145/1776893001870606336 : ℝ))/36) (((21-16)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-3909468748870903135145/1776893001870606336 : ℝ))/216) (((21-16)+2*7-5)+2) 1 7 10 x)))

def boundaryImPowerRow77_16Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk20 x=boundaryImPowerRow77_16Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((10312112752460434180081/63968148067341828096 : ℝ))/3) ((21-16)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((10312112752460434180081/63968148067341828096 : ℝ))/36) (((21-16)+2*8-5)+1) 1 8 10 x)) + ((boundaryTermPowerRow77 (7*((10312112752460434180081/63968148067341828096 : ℝ))/216) (((21-16)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-13262401795358356899695/1727139997818229358592 : ℝ))/3) ((21-16)+2*9-5) 0 9 10 x)))

def boundaryImPowerRow77_16Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk24 x=boundaryImPowerRow77_16Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-13262401795358356899695/1727139997818229358592 : ℝ))/36) (((21-16)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-13262401795358356899695/1727139997818229358592 : ℝ))/216) (((21-16)+2*9-5)+2) 1 9 10 x)) + ((boundaryTermPowerRow77 (((250827967197227695307/1151426665212152905728 : ℝ))/3) ((21-16)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((250827967197227695307/1151426665212152905728 : ℝ))/36) (((21-16)+2*10-5)+1) 1 10 10 x)))

def boundaryImPowerRow77_16Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk28 x=boundaryImPowerRow77_16Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((250827967197227695307/1151426665212152905728 : ℝ))/216) (((21-16)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-33197001440833200679/10362839986909376151552 : ℝ))/3) ((21-16)+2*11-5) 0 11 10 x)) + ((boundaryTermPowerRow77 (-((-33197001440833200679/10362839986909376151552 : ℝ))/36) (((21-16)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-33197001440833200679/10362839986909376151552 : ℝ))/216) (((21-16)+2*11-5)+2) 1 11 10 x)))

def boundaryImPowerRow77_16Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk32 x=boundaryImPowerRow77_16Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((1901628107210069351/93265559882184385363968 : ℝ))/3) ((21-16)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((1901628107210069351/93265559882184385363968 : ℝ))/36) (((21-16)+2*12-5)+1) 1 12 10 x)) + ((boundaryTermPowerRow77 (7*((1901628107210069351/93265559882184385363968 : ℝ))/216) (((21-16)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-576545030764577/10362839986909376151552 : ℝ))/3) ((21-16)+2*13-5) 0 13 10 x)))

def boundaryImPowerRow77_16Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk36 x=boundaryImPowerRow77_16Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-576545030764577/10362839986909376151552 : ℝ))/36) (((21-16)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-576545030764577/10362839986909376151552 : ℝ))/216) (((21-16)+2*13-5)+2) 1 13 10 x)) + ((boundaryTermPowerRow77 (((2362716600431/15544259980364064227328 : ℝ))/3) ((21-16)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((2362716600431/15544259980364064227328 : ℝ))/36) (((21-16)+2*14-5)+1) 1 14 10 x)))

def boundaryImPowerRow77_16Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk40 x=boundaryImPowerRow77_16Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((2362716600431/15544259980364064227328 : ℝ))/216) (((21-16)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((-58404148283/139898339823276578045952 : ℝ))/3) ((21-16)+2*15-5) 0 15 10 x)) + ((boundaryTermPowerRow77 (-((-58404148283/139898339823276578045952 : ℝ))/36) (((21-16)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((-58404148283/139898339823276578045952 : ℝ))/216) (((21-16)+2*15-5)+2) 1 15 10 x)))

def boundaryImPowerRow77_16Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk44 x=boundaryImPowerRow77_16Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((144740387/419695019469829734137856 : ℝ))/3) ((21-16)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((144740387/419695019469829734137856 : ℝ))/36) (((21-16)+2*16-5)+1) 1 16 10 x)) + ((boundaryTermPowerRow77 (7*((144740387/419695019469829734137856 : ℝ))/216) (((21-16)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((-4859/157385632301186150301696 : ℝ))/3) ((21-16)+2*17-5) 0 17 10 x)))

def boundaryImPowerRow77_16Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk48 x=boundaryImPowerRow77_16Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Chunk52 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (-((-4859/157385632301186150301696 : ℝ))/36) (((21-16)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((-4859/157385632301186150301696 : ℝ))/216) (((21-16)+2*17-5)+2) 1 17 10 x))

def boundaryImPowerRow77_16Degree10Chunk52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16Degree10Chunk52 x=c} := by

  have he : boundaryImPowerRow77_16Degree10Chunk52 x=boundaryImPowerRow77_16Degree10Chunk52 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_16Degree10Chunk52]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_16Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_16 10 x=c} := by

  have he : boundaryImPowerRow77_16 10 x=((((boundaryImPowerRow77_16Degree10Chunk0 x) + ((boundaryImPowerRow77_16Degree10Chunk4 x) + (boundaryImPowerRow77_16Degree10Chunk8 x))) + (((boundaryImPowerRow77_16Degree10Chunk12 x) + (boundaryImPowerRow77_16Degree10Chunk16 x)) + ((boundaryImPowerRow77_16Degree10Chunk20 x) + (boundaryImPowerRow77_16Degree10Chunk24 x)))) + (((boundaryImPowerRow77_16Degree10Chunk28 x) + ((boundaryImPowerRow77_16Degree10Chunk32 x) + (boundaryImPowerRow77_16Degree10Chunk36 x))) + (((boundaryImPowerRow77_16Degree10Chunk40 x) + (boundaryImPowerRow77_16Degree10Chunk44 x)) + ((boundaryImPowerRow77_16Degree10Chunk48 x) + (boundaryImPowerRow77_16Degree10Chunk52 x))))) := by

    dsimp only [boundaryImPowerRow77_16,boundaryImPowerRow77_16Degree10Chunk0,boundaryImPowerRow77_16Degree10Chunk4,boundaryImPowerRow77_16Degree10Chunk8,boundaryImPowerRow77_16Degree10Chunk12,boundaryImPowerRow77_16Degree10Chunk16,boundaryImPowerRow77_16Degree10Chunk20,boundaryImPowerRow77_16Degree10Chunk24,boundaryImPowerRow77_16Degree10Chunk28,boundaryImPowerRow77_16Degree10Chunk32,boundaryImPowerRow77_16Degree10Chunk36,boundaryImPowerRow77_16Degree10Chunk40,boundaryImPowerRow77_16Degree10Chunk44,boundaryImPowerRow77_16Degree10Chunk48,boundaryImPowerRow77_16Degree10Chunk52]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_16Degree10Chunk0Norm x).property,(boundaryImPowerRow77_16Degree10Chunk4Norm x).property,(boundaryImPowerRow77_16Degree10Chunk8Norm x).property,(boundaryImPowerRow77_16Degree10Chunk12Norm x).property,(boundaryImPowerRow77_16Degree10Chunk16Norm x).property,(boundaryImPowerRow77_16Degree10Chunk20Norm x).property,(boundaryImPowerRow77_16Degree10Chunk24Norm x).property,(boundaryImPowerRow77_16Degree10Chunk28Norm x).property,(boundaryImPowerRow77_16Degree10Chunk32Norm x).property,(boundaryImPowerRow77_16Degree10Chunk36Norm x).property,(boundaryImPowerRow77_16Degree10Chunk40Norm x).property,(boundaryImPowerRow77_16Degree10Chunk44Norm x).property,(boundaryImPowerRow77_16Degree10Chunk48Norm x).property,(boundaryImPowerRow77_16Degree10Chunk52Norm x).property]

    dsimp only [boundaryImPowerRow77_16Degree10Chunk0Norm,boundaryImPowerRow77_16Degree10Chunk4Norm,boundaryImPowerRow77_16Degree10Chunk8Norm,boundaryImPowerRow77_16Degree10Chunk12Norm,boundaryImPowerRow77_16Degree10Chunk16Norm,boundaryImPowerRow77_16Degree10Chunk20Norm,boundaryImPowerRow77_16Degree10Chunk24Norm,boundaryImPowerRow77_16Degree10Chunk28Norm,boundaryImPowerRow77_16Degree10Chunk32Norm,boundaryImPowerRow77_16Degree10Chunk36Norm,boundaryImPowerRow77_16Degree10Chunk40Norm,boundaryImPowerRow77_16Degree10Chunk44Norm,boundaryImPowerRow77_16Degree10Chunk48Norm,boundaryImPowerRow77_16Degree10Chunk52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((4243318681600/531441 : ℝ))/3) ((21-17)+2*1-5) 0 1 10 x) + (boundaryTermPowerRow77 (-((4243318681600/531441 : ℝ))/36) (((21-17)+2*1-5)+1) 1 1 10 x)) + ((boundaryTermPowerRow77 (7*((4243318681600/531441 : ℝ))/216) (((21-17)+2*1-5)+2) 1 1 10 x) + (boundaryTermPowerRow77 (((-8177048138099647/2448880128 : ℝ))/3) ((21-17)+2*2-5) 0 2 10 x)))

def boundaryImPowerRow77_17Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk0 x=boundaryImPowerRow77_17Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-8177048138099647/2448880128 : ℝ))/36) (((21-17)+2*2-5)+1) 1 2 10 x) + (boundaryTermPowerRow77 (7*((-8177048138099647/2448880128 : ℝ))/216) (((21-17)+2*2-5)+2) 1 2 10 x)) + ((boundaryTermPowerRow77 (((9851696752629245/11019960576 : ℝ))/3) ((21-17)+2*3-5) 0 3 10 x) + (boundaryTermPowerRow77 (-((9851696752629245/11019960576 : ℝ))/36) (((21-17)+2*3-5)+1) 1 3 10 x)))

def boundaryImPowerRow77_17Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk4 x=boundaryImPowerRow77_17Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((9851696752629245/11019960576 : ℝ))/216) (((21-17)+2*3-5)+2) 1 3 10 x) + (boundaryTermPowerRow77 (((-39328210763218429/198359290368 : ℝ))/3) ((21-17)+2*4-5) 0 4 10 x)) + ((boundaryTermPowerRow77 (-((-39328210763218429/198359290368 : ℝ))/36) (((21-17)+2*4-5)+1) 1 4 10 x) + (boundaryTermPowerRow77 (7*((-39328210763218429/198359290368 : ℝ))/216) (((21-17)+2*4-5)+2) 1 4 10 x)))

def boundaryImPowerRow77_17Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk8 x=boundaryImPowerRow77_17Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((2298492282801997615/57127475625984 : ℝ))/3) ((21-17)+2*5-5) 0 5 10 x) + (boundaryTermPowerRow77 (-((2298492282801997615/57127475625984 : ℝ))/36) (((21-17)+2*5-5)+1) 1 5 10 x)) + ((boundaryTermPowerRow77 (7*((2298492282801997615/57127475625984 : ℝ))/216) (((21-17)+2*5-5)+2) 1 5 10 x) + (boundaryTermPowerRow77 (((-18269417046061876823/2742118830047232 : ℝ))/3) ((21-17)+2*6-5) 0 6 10 x)))

def boundaryImPowerRow77_17Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk12 x=boundaryImPowerRow77_17Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-18269417046061876823/2742118830047232 : ℝ))/36) (((21-17)+2*6-5)+1) 1 6 10 x) + (boundaryTermPowerRow77 (7*((-18269417046061876823/2742118830047232 : ℝ))/216) (((21-17)+2*6-5)+2) 1 6 10 x)) + ((boundaryTermPowerRow77 (((116417121054948576299/148074416822550528 : ℝ))/3) ((21-17)+2*7-5) 0 7 10 x) + (boundaryTermPowerRow77 (-((116417121054948576299/148074416822550528 : ℝ))/36) (((21-17)+2*7-5)+1) 1 7 10 x)))

def boundaryImPowerRow77_17Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk16 x=boundaryImPowerRow77_17Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((116417121054948576299/148074416822550528 : ℝ))/216) (((21-17)+2*7-5)+2) 1 7 10 x) + (boundaryTermPowerRow77 (((-81442488227202758647/1332669751402954752 : ℝ))/3) ((21-17)+2*8-5) 0 8 10 x)) + ((boundaryTermPowerRow77 (-((-81442488227202758647/1332669751402954752 : ℝ))/36) (((21-17)+2*8-5)+1) 1 8 10 x) + (boundaryTermPowerRow77 (7*((-81442488227202758647/1332669751402954752 : ℝ))/216) (((21-17)+2*8-5)+2) 1 8 10 x)))

def boundaryImPowerRow77_17Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk20 x=boundaryImPowerRow77_17Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((1686909070369165695149/575713332606076452864 : ℝ))/3) ((21-17)+2*9-5) 0 9 10 x) + (boundaryTermPowerRow77 (-((1686909070369165695149/575713332606076452864 : ℝ))/36) (((21-17)+2*9-5)+1) 1 9 10 x)) + ((boundaryTermPowerRow77 (7*((1686909070369165695149/575713332606076452864 : ℝ))/216) (((21-17)+2*9-5)+2) 1 9 10 x) + (boundaryTermPowerRow77 (((-14906678686634376827/191904444202025484288 : ℝ))/3) ((21-17)+2*10-5) 0 10 10 x)))

def boundaryImPowerRow77_17Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk24 x=boundaryImPowerRow77_17Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-14906678686634376827/191904444202025484288 : ℝ))/36) (((21-17)+2*10-5)+1) 1 10 10 x) + (boundaryTermPowerRow77 (7*((-14906678686634376827/191904444202025484288 : ℝ))/216) (((21-17)+2*10-5)+2) 1 10 10 x)) + ((boundaryTermPowerRow77 (((4434303375353566451/5181419993454688075776 : ℝ))/3) ((21-17)+2*11-5) 0 11 10 x) + (boundaryTermPowerRow77 (-((4434303375353566451/5181419993454688075776 : ℝ))/36) (((21-17)+2*11-5)+1) 1 11 10 x)))

def boundaryImPowerRow77_17Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk28 x=boundaryImPowerRow77_17Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((4434303375353566451/5181419993454688075776 : ℝ))/216) (((21-17)+2*11-5)+2) 1 11 10 x) + (boundaryTermPowerRow77 (((4125741632104397/3886064995091016056832 : ℝ))/3) ((21-17)+2*12-5) 0 12 10 x)) + ((boundaryTermPowerRow77 (-((4125741632104397/3886064995091016056832 : ℝ))/36) (((21-17)+2*12-5)+1) 1 12 10 x) + (boundaryTermPowerRow77 (7*((4125741632104397/3886064995091016056832 : ℝ))/216) (((21-17)+2*12-5)+2) 1 12 10 x)))

def boundaryImPowerRow77_17Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk32 x=boundaryImPowerRow77_17Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-105581799586967/1727139997818229358592 : ℝ))/3) ((21-17)+2*13-5) 0 13 10 x) + (boundaryTermPowerRow77 (-((-105581799586967/1727139997818229358592 : ℝ))/36) (((21-17)+2*13-5)+1) 1 13 10 x)) + ((boundaryTermPowerRow77 (7*((-105581799586967/1727139997818229358592 : ℝ))/216) (((21-17)+2*13-5)+2) 1 13 10 x) + (boundaryTermPowerRow77 (((3445782008879/15544259980364064227328 : ℝ))/3) ((21-17)+2*14-5) 0 14 10 x)))

def boundaryImPowerRow77_17Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk36 x=boundaryImPowerRow77_17Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((3445782008879/15544259980364064227328 : ℝ))/36) (((21-17)+2*14-5)+1) 1 14 10 x) + (boundaryTermPowerRow77 (7*((3445782008879/15544259980364064227328 : ℝ))/216) (((21-17)+2*14-5)+2) 1 14 10 x)) + ((boundaryTermPowerRow77 (((-6081876911/46632779941092192681984 : ℝ))/3) ((21-17)+2*15-5) 0 15 10 x) + (boundaryTermPowerRow77 (-((-6081876911/46632779941092192681984 : ℝ))/36) (((21-17)+2*15-5)+1) 1 15 10 x)))

def boundaryImPowerRow77_17Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk40 x=boundaryImPowerRow77_17Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-6081876911/46632779941092192681984 : ℝ))/216) (((21-17)+2*15-5)+2) 1 15 10 x) + (boundaryTermPowerRow77 (((-1600535/17487292477909572255744 : ℝ))/3) ((21-17)+2*16-5) 0 16 10 x)) + ((boundaryTermPowerRow77 (-((-1600535/17487292477909572255744 : ℝ))/36) (((21-17)+2*16-5)+1) 1 16 10 x) + (boundaryTermPowerRow77 (7*((-1600535/17487292477909572255744 : ℝ))/216) (((21-17)+2*16-5)+2) 1 16 10 x)))

def boundaryImPowerRow77_17Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk44 x=boundaryImPowerRow77_17Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (((15397/944313793807116901810176 : ℝ))/3) ((21-17)+2*17-5) 0 17 10 x) + ((boundaryTermPowerRow77 (-((15397/944313793807116901810176 : ℝ))/36) (((21-17)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((15397/944313793807116901810176 : ℝ))/216) (((21-17)+2*17-5)+2) 1 17 10 x)))

def boundaryImPowerRow77_17Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_17Degree10Chunk48 x=boundaryImPowerRow77_17Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_17Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_17 10 x=c} := by

  have he : boundaryImPowerRow77_17 10 x=((((boundaryImPowerRow77_17Degree10Chunk0 x) + ((boundaryImPowerRow77_17Degree10Chunk4 x) + (boundaryImPowerRow77_17Degree10Chunk8 x))) + ((boundaryImPowerRow77_17Degree10Chunk12 x) + ((boundaryImPowerRow77_17Degree10Chunk16 x) + (boundaryImPowerRow77_17Degree10Chunk20 x)))) + (((boundaryImPowerRow77_17Degree10Chunk24 x) + ((boundaryImPowerRow77_17Degree10Chunk28 x) + (boundaryImPowerRow77_17Degree10Chunk32 x))) + (((boundaryImPowerRow77_17Degree10Chunk36 x) + (boundaryImPowerRow77_17Degree10Chunk40 x)) + ((boundaryImPowerRow77_17Degree10Chunk44 x) + (boundaryImPowerRow77_17Degree10Chunk48 x))))) := by

    dsimp only [boundaryImPowerRow77_17,boundaryImPowerRow77_17Degree10Chunk0,boundaryImPowerRow77_17Degree10Chunk4,boundaryImPowerRow77_17Degree10Chunk8,boundaryImPowerRow77_17Degree10Chunk12,boundaryImPowerRow77_17Degree10Chunk16,boundaryImPowerRow77_17Degree10Chunk20,boundaryImPowerRow77_17Degree10Chunk24,boundaryImPowerRow77_17Degree10Chunk28,boundaryImPowerRow77_17Degree10Chunk32,boundaryImPowerRow77_17Degree10Chunk36,boundaryImPowerRow77_17Degree10Chunk40,boundaryImPowerRow77_17Degree10Chunk44,boundaryImPowerRow77_17Degree10Chunk48]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_17Degree10Chunk0Norm x).property,(boundaryImPowerRow77_17Degree10Chunk4Norm x).property,(boundaryImPowerRow77_17Degree10Chunk8Norm x).property,(boundaryImPowerRow77_17Degree10Chunk12Norm x).property,(boundaryImPowerRow77_17Degree10Chunk16Norm x).property,(boundaryImPowerRow77_17Degree10Chunk20Norm x).property,(boundaryImPowerRow77_17Degree10Chunk24Norm x).property,(boundaryImPowerRow77_17Degree10Chunk28Norm x).property,(boundaryImPowerRow77_17Degree10Chunk32Norm x).property,(boundaryImPowerRow77_17Degree10Chunk36Norm x).property,(boundaryImPowerRow77_17Degree10Chunk40Norm x).property,(boundaryImPowerRow77_17Degree10Chunk44Norm x).property,(boundaryImPowerRow77_17Degree10Chunk48Norm x).property]

    dsimp only [boundaryImPowerRow77_17Degree10Chunk0Norm,boundaryImPowerRow77_17Degree10Chunk4Norm,boundaryImPowerRow77_17Degree10Chunk8Norm,boundaryImPowerRow77_17Degree10Chunk12Norm,boundaryImPowerRow77_17Degree10Chunk16Norm,boundaryImPowerRow77_17Degree10Chunk20Norm,boundaryImPowerRow77_17Degree10Chunk24Norm,boundaryImPowerRow77_17Degree10Chunk28Norm,boundaryImPowerRow77_17Degree10Chunk32Norm,boundaryImPowerRow77_17Degree10Chunk36Norm,boundaryImPowerRow77_17Degree10Chunk40Norm,boundaryImPowerRow77_17Degree10Chunk44Norm,boundaryImPowerRow77_17Degree10Chunk48Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((30183784448/19683 : ℝ))/3) ((21-18)+2*1-5) 0 1 10 x) + (boundaryTermPowerRow77 (-((30183784448/19683 : ℝ))/36) (((21-18)+2*1-5)+1) 1 1 10 x)) + ((boundaryTermPowerRow77 (7*((30183784448/19683 : ℝ))/216) (((21-18)+2*1-5)+2) 1 1 10 x) + (boundaryTermPowerRow77 (((-16115551352825/15116544 : ℝ))/3) ((21-18)+2*2-5) 0 2 10 x)))

def boundaryImPowerRow77_18Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk0 x=boundaryImPowerRow77_18Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-16115551352825/15116544 : ℝ))/36) (((21-18)+2*2-5)+1) 1 2 10 x) + (boundaryTermPowerRow77 (7*((-16115551352825/15116544 : ℝ))/216) (((21-18)+2*2-5)+2) 1 2 10 x)) + ((boundaryTermPowerRow77 (((3054395235517693/7346640384 : ℝ))/3) ((21-18)+2*3-5) 0 3 10 x) + (boundaryTermPowerRow77 (-((3054395235517693/7346640384 : ℝ))/36) (((21-18)+2*3-5)+1) 1 3 10 x)))

def boundaryImPowerRow77_18Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk4 x=boundaryImPowerRow77_18Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((3054395235517693/7346640384 : ℝ))/216) (((21-18)+2*3-5)+2) 1 3 10 x) + (boundaryTermPowerRow77 (((-75013329306275/816293376 : ℝ))/3) ((21-18)+2*4-5) 0 4 10 x)) + ((boundaryTermPowerRow77 (-((-75013329306275/816293376 : ℝ))/36) (((21-18)+2*4-5)+1) 1 4 10 x) + (boundaryTermPowerRow77 (7*((-75013329306275/816293376 : ℝ))/216) (((21-18)+2*4-5)+2) 1 4 10 x)))

def boundaryImPowerRow77_18Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk8 x=boundaryImPowerRow77_18Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((69537024667402933/6347497291776 : ℝ))/3) ((21-18)+2*5-5) 0 5 10 x) + (boundaryTermPowerRow77 (-((69537024667402933/6347497291776 : ℝ))/36) (((21-18)+2*5-5)+1) 1 5 10 x)) + ((boundaryTermPowerRow77 (7*((69537024667402933/6347497291776 : ℝ))/216) (((21-18)+2*5-5)+2) 1 5 10 x) + (boundaryTermPowerRow77 (((-641425827648240931/1371059415023616 : ℝ))/3) ((21-18)+2*6-5) 0 6 10 x)))

def boundaryImPowerRow77_18Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk12 x=boundaryImPowerRow77_18Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-641425827648240931/1371059415023616 : ℝ))/36) (((21-18)+2*6-5)+1) 1 6 10 x) + (boundaryTermPowerRow77 (7*((-641425827648240931/1371059415023616 : ℝ))/216) (((21-18)+2*6-5)+2) 1 6 10 x)) + ((boundaryTermPowerRow77 (((-9948386981474227/228509902503936 : ℝ))/3) ((21-18)+2*7-5) 0 7 10 x) + (boundaryTermPowerRow77 (-((-9948386981474227/228509902503936 : ℝ))/36) (((21-18)+2*7-5)+1) 1 7 10 x)))

def boundaryImPowerRow77_18Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk16 x=boundaryImPowerRow77_18Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-9948386981474227/228509902503936 : ℝ))/216) (((21-18)+2*7-5)+2) 1 7 10 x) + (boundaryTermPowerRow77 (((4106602093000574207/592297667290202112 : ℝ))/3) ((21-18)+2*8-5) 0 8 10 x)) + ((boundaryTermPowerRow77 (-((4106602093000574207/592297667290202112 : ℝ))/36) (((21-18)+2*8-5)+1) 1 8 10 x) + (boundaryTermPowerRow77 (7*((4106602093000574207/592297667290202112 : ℝ))/216) (((21-18)+2*8-5)+2) 1 8 10 x)))

def boundaryImPowerRow77_18Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk20 x=boundaryImPowerRow77_18Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-16652314821037002701/47976111050506371072 : ℝ))/3) ((21-18)+2*9-5) 0 9 10 x) + (boundaryTermPowerRow77 (-((-16652314821037002701/47976111050506371072 : ℝ))/36) (((21-18)+2*9-5)+1) 1 9 10 x)) + ((boundaryTermPowerRow77 (7*((-16652314821037002701/47976111050506371072 : ℝ))/216) (((21-18)+2*9-5)+2) 1 9 10 x) + (boundaryTermPowerRow77 (((130424793973229581/31984074033670914048 : ℝ))/3) ((21-18)+2*10-5) 0 10 10 x)))

def boundaryImPowerRow77_18Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk24 x=boundaryImPowerRow77_18Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((130424793973229581/31984074033670914048 : ℝ))/36) (((21-18)+2*10-5)+1) 1 10 10 x) + (boundaryTermPowerRow77 (7*((130424793973229581/31984074033670914048 : ℝ))/216) (((21-18)+2*10-5)+2) 1 10 10 x)) + ((boundaryTermPowerRow77 (((51066298187104675/215892499727278669824 : ℝ))/3) ((21-18)+2*11-5) 0 11 10 x) + (boundaryTermPowerRow77 (-((51066298187104675/215892499727278669824 : ℝ))/36) (((21-18)+2*11-5)+1) 1 11 10 x)))

def boundaryImPowerRow77_18Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk28 x=boundaryImPowerRow77_18Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((51066298187104675/215892499727278669824 : ℝ))/216) (((21-18)+2*11-5)+2) 1 11 10 x) + (boundaryTermPowerRow77 (((-21107016783832027/2590709996727344037888 : ℝ))/3) ((21-18)+2*12-5) 0 12 10 x)) + ((boundaryTermPowerRow77 (-((-21107016783832027/2590709996727344037888 : ℝ))/36) (((21-18)+2*12-5)+1) 1 12 10 x) + (boundaryTermPowerRow77 (7*((-21107016783832027/2590709996727344037888 : ℝ))/216) (((21-18)+2*12-5)+2) 1 12 10 x)))

def boundaryImPowerRow77_18Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk32 x=boundaryImPowerRow77_18Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((24039534658013/287856666303038226432 : ℝ))/3) ((21-18)+2*13-5) 0 13 10 x) + (boundaryTermPowerRow77 (-((24039534658013/287856666303038226432 : ℝ))/36) (((21-18)+2*13-5)+1) 1 13 10 x)) + ((boundaryTermPowerRow77 (7*((24039534658013/287856666303038226432 : ℝ))/216) (((21-18)+2*13-5)+2) 1 13 10 x) + (boundaryTermPowerRow77 (((-203854763177/647677499181836009472 : ℝ))/3) ((21-18)+2*14-5) 0 14 10 x)))

def boundaryImPowerRow77_18Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk36 x=boundaryImPowerRow77_18Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-203854763177/647677499181836009472 : ℝ))/36) (((21-18)+2*14-5)+1) 1 14 10 x) + (boundaryTermPowerRow77 (7*((-203854763177/647677499181836009472 : ℝ))/216) (((21-18)+2*14-5)+2) 1 14 10 x)) + ((boundaryTermPowerRow77 (((3249860191/7772129990182032113664 : ℝ))/3) ((21-18)+2*15-5) 0 15 10 x) + (boundaryTermPowerRow77 (-((3249860191/7772129990182032113664 : ℝ))/36) (((21-18)+2*15-5)+1) 1 15 10 x)))

def boundaryImPowerRow77_18Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk40 x=boundaryImPowerRow77_18Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((3249860191/7772129990182032113664 : ℝ))/216) (((21-18)+2*15-5)+2) 1 15 10 x) + (boundaryTermPowerRow77 (((-1323349/8743646238954786127872 : ℝ))/3) ((21-18)+2*16-5) 0 16 10 x)) + ((boundaryTermPowerRow77 (-((-1323349/8743646238954786127872 : ℝ))/36) (((21-18)+2*16-5)+1) 1 16 10 x) + (boundaryTermPowerRow77 (7*((-1323349/8743646238954786127872 : ℝ))/216) (((21-18)+2*16-5)+2) 1 16 10 x)))

def boundaryImPowerRow77_18Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk44 x=boundaryImPowerRow77_18Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Chunk48 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 (((245/39346408075296537575424 : ℝ))/3) ((21-18)+2*17-5) 0 17 10 x) + ((boundaryTermPowerRow77 (-((245/39346408075296537575424 : ℝ))/36) (((21-18)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((245/39346408075296537575424 : ℝ))/216) (((21-18)+2*17-5)+2) 1 17 10 x)))

def boundaryImPowerRow77_18Degree10Chunk48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18Degree10Chunk48 x=c} := by

  have he : boundaryImPowerRow77_18Degree10Chunk48 x=boundaryImPowerRow77_18Degree10Chunk48 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Chunk48]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_18Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_18 10 x=c} := by

  have he : boundaryImPowerRow77_18 10 x=((((boundaryImPowerRow77_18Degree10Chunk0 x) + ((boundaryImPowerRow77_18Degree10Chunk4 x) + (boundaryImPowerRow77_18Degree10Chunk8 x))) + ((boundaryImPowerRow77_18Degree10Chunk12 x) + ((boundaryImPowerRow77_18Degree10Chunk16 x) + (boundaryImPowerRow77_18Degree10Chunk20 x)))) + (((boundaryImPowerRow77_18Degree10Chunk24 x) + ((boundaryImPowerRow77_18Degree10Chunk28 x) + (boundaryImPowerRow77_18Degree10Chunk32 x))) + (((boundaryImPowerRow77_18Degree10Chunk36 x) + (boundaryImPowerRow77_18Degree10Chunk40 x)) + ((boundaryImPowerRow77_18Degree10Chunk44 x) + (boundaryImPowerRow77_18Degree10Chunk48 x))))) := by

    dsimp only [boundaryImPowerRow77_18,boundaryImPowerRow77_18Degree10Chunk0,boundaryImPowerRow77_18Degree10Chunk4,boundaryImPowerRow77_18Degree10Chunk8,boundaryImPowerRow77_18Degree10Chunk12,boundaryImPowerRow77_18Degree10Chunk16,boundaryImPowerRow77_18Degree10Chunk20,boundaryImPowerRow77_18Degree10Chunk24,boundaryImPowerRow77_18Degree10Chunk28,boundaryImPowerRow77_18Degree10Chunk32,boundaryImPowerRow77_18Degree10Chunk36,boundaryImPowerRow77_18Degree10Chunk40,boundaryImPowerRow77_18Degree10Chunk44,boundaryImPowerRow77_18Degree10Chunk48]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_18Degree10Chunk0Norm x).property,(boundaryImPowerRow77_18Degree10Chunk4Norm x).property,(boundaryImPowerRow77_18Degree10Chunk8Norm x).property,(boundaryImPowerRow77_18Degree10Chunk12Norm x).property,(boundaryImPowerRow77_18Degree10Chunk16Norm x).property,(boundaryImPowerRow77_18Degree10Chunk20Norm x).property,(boundaryImPowerRow77_18Degree10Chunk24Norm x).property,(boundaryImPowerRow77_18Degree10Chunk28Norm x).property,(boundaryImPowerRow77_18Degree10Chunk32Norm x).property,(boundaryImPowerRow77_18Degree10Chunk36Norm x).property,(boundaryImPowerRow77_18Degree10Chunk40Norm x).property,(boundaryImPowerRow77_18Degree10Chunk44Norm x).property,(boundaryImPowerRow77_18Degree10Chunk48Norm x).property]

    dsimp only [boundaryImPowerRow77_18Degree10Chunk0Norm,boundaryImPowerRow77_18Degree10Chunk4Norm,boundaryImPowerRow77_18Degree10Chunk8Norm,boundaryImPowerRow77_18Degree10Chunk12Norm,boundaryImPowerRow77_18Degree10Chunk16Norm,boundaryImPowerRow77_18Degree10Chunk20Norm,boundaryImPowerRow77_18Degree10Chunk24Norm,boundaryImPowerRow77_18Degree10Chunk28Norm,boundaryImPowerRow77_18Degree10Chunk32Norm,boundaryImPowerRow77_18Degree10Chunk36Norm,boundaryImPowerRow77_18Degree10Chunk40Norm,boundaryImPowerRow77_18Degree10Chunk44Norm,boundaryImPowerRow77_18Degree10Chunk48Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((29795377108907/34012224 : ℝ))/3) ((21-19)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((29795377108907/34012224 : ℝ))/36) (((21-19)+2*2-5)+1) 1 2 10 x)) + ((boundaryTermPowerRow77 (7*((29795377108907/34012224 : ℝ))/216) (((21-19)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((-437897528894045/1224440064 : ℝ))/3) ((21-19)+2*3-5) 0 3 10 x)))

def boundaryImPowerRow77_19Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk0 x=boundaryImPowerRow77_19Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-437897528894045/1224440064 : ℝ))/36) (((21-19)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((-437897528894045/1224440064 : ℝ))/216) (((21-19)+2*3-5)+2) 1 3 10 x)) + ((boundaryTermPowerRow77 (((15644466017518031/176319369216 : ℝ))/3) ((21-19)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((15644466017518031/176319369216 : ℝ))/36) (((21-19)+2*4-5)+1) 1 4 10 x)))

def boundaryImPowerRow77_19Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk4 x=boundaryImPowerRow77_19Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((15644466017518031/176319369216 : ℝ))/216) (((21-19)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((-90981090116776051/6347497291776 : ℝ))/3) ((21-19)+2*5-5) 0 5 10 x)) + ((boundaryTermPowerRow77 (-((-90981090116776051/6347497291776 : ℝ))/36) (((21-19)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((-90981090116776051/6347497291776 : ℝ))/216) (((21-19)+2*5-5)+2) 1 5 10 x)))

def boundaryImPowerRow77_19Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk8 x=boundaryImPowerRow77_19Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((120098757160894523/76169967501312 : ℝ))/3) ((21-19)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((120098757160894523/76169967501312 : ℝ))/36) (((21-19)+2*6-5)+1) 1 6 10 x)) + ((boundaryTermPowerRow77 (7*((120098757160894523/76169967501312 : ℝ))/216) (((21-19)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((-507242181469983599/4113178245070848 : ℝ))/3) ((21-19)+2*7-5) 0 7 10 x)))

def boundaryImPowerRow77_19Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk12 x=boundaryImPowerRow77_19Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-507242181469983599/4113178245070848 : ℝ))/36) (((21-19)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((-507242181469983599/4113178245070848 : ℝ))/216) (((21-19)+2*7-5)+2) 1 7 10 x)) + ((boundaryTermPowerRow77 (((2156268021145190891/296148833645101056 : ℝ))/3) ((21-19)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((2156268021145190891/296148833645101056 : ℝ))/36) (((21-19)+2*8-5)+1) 1 8 10 x)))

def boundaryImPowerRow77_19Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk16 x=boundaryImPowerRow77_19Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((2156268021145190891/296148833645101056 : ℝ))/216) (((21-19)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((-693695452583458339/1999004627104432128 : ℝ))/3) ((21-19)+2*9-5) 0 9 10 x)) + ((boundaryTermPowerRow77 (-((-693695452583458339/1999004627104432128 : ℝ))/36) (((21-19)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((-693695452583458339/1999004627104432128 : ℝ))/216) (((21-19)+2*9-5)+2) 1 9 10 x)))

def boundaryImPowerRow77_19Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk20 x=boundaryImPowerRow77_19Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((1115739130466579/83291859462684672 : ℝ))/3) ((21-19)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((1115739130466579/83291859462684672 : ℝ))/36) (((21-19)+2*10-5)+1) 1 10 10 x)) + ((boundaryTermPowerRow77 (7*((1115739130466579/83291859462684672 : ℝ))/216) (((21-19)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((-17933669805700133/47976111050506371072 : ℝ))/3) ((21-19)+2*11-5) 0 11 10 x)))

def boundaryImPowerRow77_19Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk24 x=boundaryImPowerRow77_19Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-17933669805700133/47976111050506371072 : ℝ))/36) (((21-19)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((-17933669805700133/47976111050506371072 : ℝ))/216) (((21-19)+2*11-5)+2) 1 11 10 x)) + ((boundaryTermPowerRow77 (((2719178938354451/431784999454557339648 : ℝ))/3) ((21-19)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((2719178938354451/431784999454557339648 : ℝ))/36) (((21-19)+2*12-5)+1) 1 12 10 x)))

def boundaryImPowerRow77_19Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk28 x=boundaryImPowerRow77_19Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((2719178938354451/431784999454557339648 : ℝ))/216) (((21-19)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((-1297901232197/23988055525253185536 : ℝ))/3) ((21-19)+2*13-5) 0 13 10 x)) + ((boundaryTermPowerRow77 (-((-1297901232197/23988055525253185536 : ℝ))/36) (((21-19)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((-1297901232197/23988055525253185536 : ℝ))/216) (((21-19)+2*13-5)+2) 1 13 10 x)))

def boundaryImPowerRow77_19Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk32 x=boundaryImPowerRow77_19Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((15237188201/71964166575759556608 : ℝ))/3) ((21-19)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((15237188201/71964166575759556608 : ℝ))/36) (((21-19)+2*14-5)+1) 1 14 10 x)) + ((boundaryTermPowerRow77 (7*((15237188201/71964166575759556608 : ℝ))/216) (((21-19)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((-1299579569/3886064995091016056832 : ℝ))/3) ((21-19)+2*15-5) 0 15 10 x)))

def boundaryImPowerRow77_19Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk36 x=boundaryImPowerRow77_19Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((-1299579569/3886064995091016056832 : ℝ))/36) (((21-19)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((-1299579569/3886064995091016056832 : ℝ))/216) (((21-19)+2*15-5)+2) 1 15 10 x)) + ((boundaryTermPowerRow77 (((638777/3886064995091016056832 : ℝ))/3) ((21-19)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((638777/3886064995091016056832 : ℝ))/36) (((21-19)+2*16-5)+1) 1 16 10 x)))

def boundaryImPowerRow77_19Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk40 x=boundaryImPowerRow77_19Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((638777/3886064995091016056832 : ℝ))/216) (((21-19)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((-47/4371823119477393063936 : ℝ))/3) ((21-19)+2*17-5) 0 17 10 x)) + ((boundaryTermPowerRow77 (-((-47/4371823119477393063936 : ℝ))/36) (((21-19)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((-47/4371823119477393063936 : ℝ))/216) (((21-19)+2*17-5)+2) 1 17 10 x)))

def boundaryImPowerRow77_19Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_19Degree10Chunk44 x=boundaryImPowerRow77_19Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_19Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_19Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_19 10 x=c} := by

  have he : boundaryImPowerRow77_19 10 x=((((boundaryImPowerRow77_19Degree10Chunk0 x) + ((boundaryImPowerRow77_19Degree10Chunk4 x) + (boundaryImPowerRow77_19Degree10Chunk8 x))) + ((boundaryImPowerRow77_19Degree10Chunk12 x) + ((boundaryImPowerRow77_19Degree10Chunk16 x) + (boundaryImPowerRow77_19Degree10Chunk20 x)))) + (((boundaryImPowerRow77_19Degree10Chunk24 x) + ((boundaryImPowerRow77_19Degree10Chunk28 x) + (boundaryImPowerRow77_19Degree10Chunk32 x))) + ((boundaryImPowerRow77_19Degree10Chunk36 x) + ((boundaryImPowerRow77_19Degree10Chunk40 x) + (boundaryImPowerRow77_19Degree10Chunk44 x))))) := by

    dsimp only [boundaryImPowerRow77_19,boundaryImPowerRow77_19Degree10Chunk0,boundaryImPowerRow77_19Degree10Chunk4,boundaryImPowerRow77_19Degree10Chunk8,boundaryImPowerRow77_19Degree10Chunk12,boundaryImPowerRow77_19Degree10Chunk16,boundaryImPowerRow77_19Degree10Chunk20,boundaryImPowerRow77_19Degree10Chunk24,boundaryImPowerRow77_19Degree10Chunk28,boundaryImPowerRow77_19Degree10Chunk32,boundaryImPowerRow77_19Degree10Chunk36,boundaryImPowerRow77_19Degree10Chunk40,boundaryImPowerRow77_19Degree10Chunk44]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_19Degree10Chunk0Norm x).property,(boundaryImPowerRow77_19Degree10Chunk4Norm x).property,(boundaryImPowerRow77_19Degree10Chunk8Norm x).property,(boundaryImPowerRow77_19Degree10Chunk12Norm x).property,(boundaryImPowerRow77_19Degree10Chunk16Norm x).property,(boundaryImPowerRow77_19Degree10Chunk20Norm x).property,(boundaryImPowerRow77_19Degree10Chunk24Norm x).property,(boundaryImPowerRow77_19Degree10Chunk28Norm x).property,(boundaryImPowerRow77_19Degree10Chunk32Norm x).property,(boundaryImPowerRow77_19Degree10Chunk36Norm x).property,(boundaryImPowerRow77_19Degree10Chunk40Norm x).property,(boundaryImPowerRow77_19Degree10Chunk44Norm x).property]

    dsimp only [boundaryImPowerRow77_19Degree10Chunk0Norm,boundaryImPowerRow77_19Degree10Chunk4Norm,boundaryImPowerRow77_19Degree10Chunk8Norm,boundaryImPowerRow77_19Degree10Chunk12Norm,boundaryImPowerRow77_19Degree10Chunk16Norm,boundaryImPowerRow77_19Degree10Chunk20Norm,boundaryImPowerRow77_19Degree10Chunk24Norm,boundaryImPowerRow77_19Degree10Chunk28Norm,boundaryImPowerRow77_19Degree10Chunk32Norm,boundaryImPowerRow77_19Degree10Chunk36Norm,boundaryImPowerRow77_19Degree10Chunk40Norm,boundaryImPowerRow77_19Degree10Chunk44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-82847596544/177147 : ℝ))/3) ((21-20)+2*2-5) 0 2 10 x) + (boundaryTermPowerRow77 (-((-82847596544/177147 : ℝ))/36) (((21-20)+2*2-5)+1) 1 2 10 x)) + ((boundaryTermPowerRow77 (7*((-82847596544/177147 : ℝ))/216) (((21-20)+2*2-5)+2) 1 2 10 x) + (boundaryTermPowerRow77 (((4398482249537/25509168 : ℝ))/3) ((21-20)+2*3-5) 0 3 10 x)))

def boundaryImPowerRow77_20Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk0 x=boundaryImPowerRow77_20Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((4398482249537/25509168 : ℝ))/36) (((21-20)+2*3-5)+1) 1 3 10 x) + (boundaryTermPowerRow77 (7*((4398482249537/25509168 : ℝ))/216) (((21-20)+2*3-5)+2) 1 3 10 x)) + ((boundaryTermPowerRow77 (((-76317551083573/1836660096 : ℝ))/3) ((21-20)+2*4-5) 0 4 10 x) + (boundaryTermPowerRow77 (-((-76317551083573/1836660096 : ℝ))/36) (((21-20)+2*4-5)+1) 1 4 10 x)))

def boundaryImPowerRow77_20Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk4 x=boundaryImPowerRow77_20Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-76317551083573/1836660096 : ℝ))/216) (((21-20)+2*4-5)+2) 1 4 10 x) + (boundaryTermPowerRow77 (((114351004022381/16529940864 : ℝ))/3) ((21-20)+2*5-5) 0 5 10 x)) + ((boundaryTermPowerRow77 (-((114351004022381/16529940864 : ℝ))/36) (((21-20)+2*5-5)+1) 1 5 10 x) + (boundaryTermPowerRow77 (7*((114351004022381/16529940864 : ℝ))/216) (((21-20)+2*5-5)+2) 1 5 10 x)))

def boundaryImPowerRow77_20Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk8 x=boundaryImPowerRow77_20Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-1304943382921777/1586874322944 : ℝ))/3) ((21-20)+2*6-5) 0 6 10 x) + (boundaryTermPowerRow77 (-((-1304943382921777/1586874322944 : ℝ))/36) (((21-20)+2*6-5)+1) 1 6 10 x)) + ((boundaryTermPowerRow77 (7*((-1304943382921777/1586874322944 : ℝ))/216) (((21-20)+2*6-5)+2) 1 6 10 x) + (boundaryTermPowerRow77 (((12206930250593419/171382426877952 : ℝ))/3) ((21-20)+2*7-5) 0 7 10 x)))

def boundaryImPowerRow77_20Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk12 x=boundaryImPowerRow77_20Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((12206930250593419/171382426877952 : ℝ))/36) (((21-20)+2*7-5)+1) 1 7 10 x) + (boundaryTermPowerRow77 (7*((12206930250593419/171382426877952 : ℝ))/216) (((21-20)+2*7-5)+2) 1 7 10 x)) + ((boundaryTermPowerRow77 (((-7004604422418047/1542441841901568 : ℝ))/3) ((21-20)+2*8-5) 0 8 10 x) + (boundaryTermPowerRow77 (-((-7004604422418047/1542441841901568 : ℝ))/36) (((21-20)+2*8-5)+1) 1 8 10 x)))

def boundaryImPowerRow77_20Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk16 x=boundaryImPowerRow77_20Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-7004604422418047/1542441841901568 : ℝ))/216) (((21-20)+2*8-5)+2) 1 8 10 x) + (boundaryTermPowerRow77 (((141722042087919145/666334875701477376 : ℝ))/3) ((21-20)+2*9-5) 0 9 10 x)) + ((boundaryTermPowerRow77 (-((141722042087919145/666334875701477376 : ℝ))/36) (((21-20)+2*9-5)+1) 1 9 10 x) + (boundaryTermPowerRow77 (7*((141722042087919145/666334875701477376 : ℝ))/216) (((21-20)+2*9-5)+2) 1 9 10 x)))

def boundaryImPowerRow77_20Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk20 x=boundaryImPowerRow77_20Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-3182611997616607/444223250467651584 : ℝ))/3) ((21-20)+2*10-5) 0 10 10 x) + (boundaryTermPowerRow77 (-((-3182611997616607/444223250467651584 : ℝ))/36) (((21-20)+2*10-5)+1) 1 10 10 x)) + ((boundaryTermPowerRow77 (7*((-3182611997616607/444223250467651584 : ℝ))/216) (((21-20)+2*10-5)+2) 1 10 10 x) + (boundaryTermPowerRow77 (((1980514142210113/11994027762626592768 : ℝ))/3) ((21-20)+2*11-5) 0 11 10 x)))

def boundaryImPowerRow77_20Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk24 x=boundaryImPowerRow77_20Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((1980514142210113/11994027762626592768 : ℝ))/36) (((21-20)+2*11-5)+1) 1 11 10 x) + (boundaryTermPowerRow77 (7*((1980514142210113/11994027762626592768 : ℝ))/216) (((21-20)+2*11-5)+2) 1 11 10 x)) + ((boundaryTermPowerRow77 (((-171678661461703/71964166575759556608 : ℝ))/3) ((21-20)+2*12-5) 0 12 10 x) + (boundaryTermPowerRow77 (-((-171678661461703/71964166575759556608 : ℝ))/36) (((21-20)+2*12-5)+1) 1 12 10 x)))

def boundaryImPowerRow77_20Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk28 x=boundaryImPowerRow77_20Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-171678661461703/71964166575759556608 : ℝ))/216) (((21-20)+2*12-5)+2) 1 12 10 x) + (boundaryTermPowerRow77 (((12789770267/666334875701477376 : ℝ))/3) ((21-20)+2*13-5) 0 13 10 x)) + ((boundaryTermPowerRow77 (-((12789770267/666334875701477376 : ℝ))/36) (((21-20)+2*13-5)+1) 1 13 10 x) + (boundaryTermPowerRow77 (7*((12789770267/666334875701477376 : ℝ))/216) (((21-20)+2*13-5)+2) 1 13 10 x)))

def boundaryImPowerRow77_20Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk32 x=boundaryImPowerRow77_20Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-2047532911/26986562465909833728 : ℝ))/3) ((21-20)+2*14-5) 0 14 10 x) + (boundaryTermPowerRow77 (-((-2047532911/26986562465909833728 : ℝ))/36) (((21-20)+2*14-5)+1) 1 14 10 x)) + ((boundaryTermPowerRow77 (7*((-2047532911/26986562465909833728 : ℝ))/216) (((21-20)+2*14-5)+2) 1 14 10 x) + (boundaryTermPowerRow77 (((40807745/323838749590918004736 : ℝ))/3) ((21-20)+2*15-5) 0 15 10 x)))

def boundaryImPowerRow77_20Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk36 x=boundaryImPowerRow77_20Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((40807745/323838749590918004736 : ℝ))/36) (((21-20)+2*15-5)+1) 1 15 10 x) + (boundaryTermPowerRow77 (7*((40807745/323838749590918004736 : ℝ))/216) (((21-20)+2*15-5)+2) 1 15 10 x)) + ((boundaryTermPowerRow77 (((-4747/71964166575759556608 : ℝ))/3) ((21-20)+2*16-5) 0 16 10 x) + (boundaryTermPowerRow77 (-((-4747/71964166575759556608 : ℝ))/36) (((21-20)+2*16-5)+1) 1 16 10 x)))

def boundaryImPowerRow77_20Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk40 x=boundaryImPowerRow77_20Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-4747/71964166575759556608 : ℝ))/216) (((21-20)+2*16-5)+2) 1 16 10 x) + (boundaryTermPowerRow77 (((5/1092955779869348265984 : ℝ))/3) ((21-20)+2*17-5) 0 17 10 x)) + ((boundaryTermPowerRow77 (-((5/1092955779869348265984 : ℝ))/36) (((21-20)+2*17-5)+1) 1 17 10 x) + (boundaryTermPowerRow77 (7*((5/1092955779869348265984 : ℝ))/216) (((21-20)+2*17-5)+2) 1 17 10 x)))

def boundaryImPowerRow77_20Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_20Degree10Chunk44 x=boundaryImPowerRow77_20Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_20Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_20 10 x=c} := by

  have he : boundaryImPowerRow77_20 10 x=((((boundaryImPowerRow77_20Degree10Chunk0 x) + ((boundaryImPowerRow77_20Degree10Chunk4 x) + (boundaryImPowerRow77_20Degree10Chunk8 x))) + ((boundaryImPowerRow77_20Degree10Chunk12 x) + ((boundaryImPowerRow77_20Degree10Chunk16 x) + (boundaryImPowerRow77_20Degree10Chunk20 x)))) + (((boundaryImPowerRow77_20Degree10Chunk24 x) + ((boundaryImPowerRow77_20Degree10Chunk28 x) + (boundaryImPowerRow77_20Degree10Chunk32 x))) + ((boundaryImPowerRow77_20Degree10Chunk36 x) + ((boundaryImPowerRow77_20Degree10Chunk40 x) + (boundaryImPowerRow77_20Degree10Chunk44 x))))) := by

    dsimp only [boundaryImPowerRow77_20,boundaryImPowerRow77_20Degree10Chunk0,boundaryImPowerRow77_20Degree10Chunk4,boundaryImPowerRow77_20Degree10Chunk8,boundaryImPowerRow77_20Degree10Chunk12,boundaryImPowerRow77_20Degree10Chunk16,boundaryImPowerRow77_20Degree10Chunk20,boundaryImPowerRow77_20Degree10Chunk24,boundaryImPowerRow77_20Degree10Chunk28,boundaryImPowerRow77_20Degree10Chunk32,boundaryImPowerRow77_20Degree10Chunk36,boundaryImPowerRow77_20Degree10Chunk40,boundaryImPowerRow77_20Degree10Chunk44]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_20Degree10Chunk0Norm x).property,(boundaryImPowerRow77_20Degree10Chunk4Norm x).property,(boundaryImPowerRow77_20Degree10Chunk8Norm x).property,(boundaryImPowerRow77_20Degree10Chunk12Norm x).property,(boundaryImPowerRow77_20Degree10Chunk16Norm x).property,(boundaryImPowerRow77_20Degree10Chunk20Norm x).property,(boundaryImPowerRow77_20Degree10Chunk24Norm x).property,(boundaryImPowerRow77_20Degree10Chunk28Norm x).property,(boundaryImPowerRow77_20Degree10Chunk32Norm x).property,(boundaryImPowerRow77_20Degree10Chunk36Norm x).property,(boundaryImPowerRow77_20Degree10Chunk40Norm x).property,(boundaryImPowerRow77_20Degree10Chunk44Norm x).property]

    dsimp only [boundaryImPowerRow77_20Degree10Chunk0Norm,boundaryImPowerRow77_20Degree10Chunk4Norm,boundaryImPowerRow77_20Degree10Chunk8Norm,boundaryImPowerRow77_20Degree10Chunk12Norm,boundaryImPowerRow77_20Degree10Chunk16Norm,boundaryImPowerRow77_20Degree10Chunk20Norm,boundaryImPowerRow77_20Degree10Chunk24Norm,boundaryImPowerRow77_20Degree10Chunk28Norm,boundaryImPowerRow77_20Degree10Chunk32Norm,boundaryImPowerRow77_20Degree10Chunk36Norm,boundaryImPowerRow77_20Degree10Chunk40Norm,boundaryImPowerRow77_20Degree10Chunk44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-2116157440/59049 : ℝ))/3) ((21-21)+2*3-5) 0 3 10 x) + (boundaryTermPowerRow77 (-((-2116157440/59049 : ℝ))/36) (((21-21)+2*3-5)+1) 1 3 10 x)) + ((boundaryTermPowerRow77 (7*((-2116157440/59049 : ℝ))/216) (((21-21)+2*3-5)+2) 1 3 10 x) + (boundaryTermPowerRow77 (((40487047168/4782969 : ℝ))/3) ((21-21)+2*4-5) 0 4 10 x)))

def boundaryImPowerRow77_21Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk0 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk0 x=boundaryImPowerRow77_21Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((40487047168/4782969 : ℝ))/36) (((21-21)+2*4-5)+1) 1 4 10 x) + (boundaryTermPowerRow77 (7*((40487047168/4782969 : ℝ))/216) (((21-21)+2*4-5)+2) 1 4 10 x)) + ((boundaryTermPowerRow77 (((-60155799296/43046721 : ℝ))/3) ((21-21)+2*5-5) 0 5 10 x) + (boundaryTermPowerRow77 (-((-60155799296/43046721 : ℝ))/36) (((21-21)+2*5-5)+1) 1 5 10 x)))

def boundaryImPowerRow77_21Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk4 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk4 x=boundaryImPowerRow77_21Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-60155799296/43046721 : ℝ))/216) (((21-21)+2*5-5)+2) 1 5 10 x) + (boundaryTermPowerRow77 (((16458456017087/99179645184 : ℝ))/3) ((21-21)+2*6-5) 0 6 10 x)) + ((boundaryTermPowerRow77 (-((16458456017087/99179645184 : ℝ))/36) (((21-21)+2*6-5)+1) 1 6 10 x) + (boundaryTermPowerRow77 (7*((16458456017087/99179645184 : ℝ))/216) (((21-21)+2*6-5)+2) 1 6 10 x)))

def boundaryImPowerRow77_21Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk8 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk8 x=boundaryImPowerRow77_21Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-3202435542593/223154201664 : ℝ))/3) ((21-21)+2*7-5) 0 7 10 x) + (boundaryTermPowerRow77 (-((-3202435542593/223154201664 : ℝ))/36) (((21-21)+2*7-5)+1) 1 7 10 x)) + ((boundaryTermPowerRow77 (7*((-3202435542593/223154201664 : ℝ))/216) (((21-21)+2*7-5)+2) 1 7 10 x) + (boundaryTermPowerRow77 (((464622800108815/514147280633856 : ℝ))/3) ((21-21)+2*8-5) 0 8 10 x)))

def boundaryImPowerRow77_21Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk12 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk12 x=boundaryImPowerRow77_21Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((464622800108815/514147280633856 : ℝ))/36) (((21-21)+2*8-5)+1) 1 8 10 x) + (boundaryTermPowerRow77 (7*((464622800108815/514147280633856 : ℝ))/216) (((21-21)+2*8-5)+2) 1 8 10 x)) + ((boundaryTermPowerRow77 (((-2273787291250585/55527906308456448 : ℝ))/3) ((21-21)+2*9-5) 0 9 10 x) + (boundaryTermPowerRow77 (-((-2273787291250585/55527906308456448 : ℝ))/36) (((21-21)+2*9-5)+1) 1 9 10 x)))

def boundaryImPowerRow77_21Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk16 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk16 x=boundaryImPowerRow77_21Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk20 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-2273787291250585/55527906308456448 : ℝ))/216) (((21-21)+2*9-5)+2) 1 9 10 x) + (boundaryTermPowerRow77 (((96411338058443/74037208411275264 : ℝ))/3) ((21-21)+2*10-5) 0 10 10 x)) + ((boundaryTermPowerRow77 (-((96411338058443/74037208411275264 : ℝ))/36) (((21-21)+2*10-5)+1) 1 10 10 x) + (boundaryTermPowerRow77 (7*((96411338058443/74037208411275264 : ℝ))/216) (((21-21)+2*10-5)+2) 1 10 10 x)))

def boundaryImPowerRow77_21Degree10Chunk20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk20 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk20 x=boundaryImPowerRow77_21Degree10Chunk20 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk20]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk24 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-27853481344505/999502313552216064 : ℝ))/3) ((21-21)+2*11-5) 0 11 10 x) + (boundaryTermPowerRow77 (-((-27853481344505/999502313552216064 : ℝ))/36) (((21-21)+2*11-5)+1) 1 11 10 x)) + ((boundaryTermPowerRow77 (7*((-27853481344505/999502313552216064 : ℝ))/216) (((21-21)+2*11-5)+2) 1 11 10 x) + (boundaryTermPowerRow77 (((140944386775/374813367582081024 : ℝ))/3) ((21-21)+2*12-5) 0 12 10 x)))

def boundaryImPowerRow77_21Degree10Chunk24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk24 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk24 x=boundaryImPowerRow77_21Degree10Chunk24 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk24]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk28 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((140944386775/374813367582081024 : ℝ))/36) (((21-21)+2*12-5)+1) 1 12 10 x) + (boundaryTermPowerRow77 (7*((140944386775/374813367582081024 : ℝ))/216) (((21-21)+2*12-5)+2) 1 12 10 x)) + ((boundaryTermPowerRow77 (((-5818211165/1999004627104432128 : ℝ))/3) ((21-21)+2*13-5) 0 13 10 x) + (boundaryTermPowerRow77 (-((-5818211165/1999004627104432128 : ℝ))/36) (((21-21)+2*13-5)+1) 1 13 10 x)))

def boundaryImPowerRow77_21Degree10Chunk28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk28 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk28 x=boundaryImPowerRow77_21Degree10Chunk28 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk28]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk32 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (7*((-5818211165/1999004627104432128 : ℝ))/216) (((21-21)+2*13-5)+2) 1 13 10 x) + (boundaryTermPowerRow77 (((204815881/17991041643939889152 : ℝ))/3) ((21-21)+2*14-5) 0 14 10 x)) + ((boundaryTermPowerRow77 (-((204815881/17991041643939889152 : ℝ))/36) (((21-21)+2*14-5)+1) 1 14 10 x) + (boundaryTermPowerRow77 (7*((204815881/17991041643939889152 : ℝ))/216) (((21-21)+2*14-5)+2) 1 14 10 x)))

def boundaryImPowerRow77_21Degree10Chunk32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk32 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk32 x=boundaryImPowerRow77_21Degree10Chunk32 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk32]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk36 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (((-255391/13493281232954916864 : ℝ))/3) ((21-21)+2*15-5) 0 15 10 x) + (boundaryTermPowerRow77 (-((-255391/13493281232954916864 : ℝ))/36) (((21-21)+2*15-5)+1) 1 15 10 x)) + ((boundaryTermPowerRow77 (7*((-255391/13493281232954916864 : ℝ))/216) (((21-21)+2*15-5)+2) 1 15 10 x) + (boundaryTermPowerRow77 (((803/80959687397729501184 : ℝ))/3) ((21-21)+2*16-5) 0 16 10 x)))

def boundaryImPowerRow77_21Degree10Chunk36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk36 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk36 x=boundaryImPowerRow77_21Degree10Chunk36 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk36]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk40 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 (-((803/80959687397729501184 : ℝ))/36) (((21-21)+2*16-5)+1) 1 16 10 x) + (boundaryTermPowerRow77 (7*((803/80959687397729501184 : ℝ))/216) (((21-21)+2*16-5)+2) 1 16 10 x)) + ((boundaryTermPowerRow77 (((-1/1457274373159131021312 : ℝ))/3) ((21-21)+2*17-5) 0 17 10 x) + (boundaryTermPowerRow77 (-((-1/1457274373159131021312 : ℝ))/36) (((21-21)+2*17-5)+1) 1 17 10 x)))

def boundaryImPowerRow77_21Degree10Chunk40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk40 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk40 x=boundaryImPowerRow77_21Degree10Chunk40 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk40]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Chunk44 (x : ℕ → ℝ) : ℝ :=
  (boundaryTermPowerRow77 (7*((-1/1457274373159131021312 : ℝ))/216) (((21-21)+2*17-5)+2) 1 17 10 x)

def boundaryImPowerRow77_21Degree10Chunk44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21Degree10Chunk44 x=c} := by

  have he : boundaryImPowerRow77_21Degree10Chunk44 x=boundaryImPowerRow77_21Degree10Chunk44 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Chunk44]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryImPowerRow77_21Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryImPowerRow77_21 10 x=c} := by

  have he : boundaryImPowerRow77_21 10 x=((((boundaryImPowerRow77_21Degree10Chunk0 x) + ((boundaryImPowerRow77_21Degree10Chunk4 x) + (boundaryImPowerRow77_21Degree10Chunk8 x))) + ((boundaryImPowerRow77_21Degree10Chunk12 x) + ((boundaryImPowerRow77_21Degree10Chunk16 x) + (boundaryImPowerRow77_21Degree10Chunk20 x)))) + (((boundaryImPowerRow77_21Degree10Chunk24 x) + ((boundaryImPowerRow77_21Degree10Chunk28 x) + (boundaryImPowerRow77_21Degree10Chunk32 x))) + ((boundaryImPowerRow77_21Degree10Chunk36 x) + ((boundaryImPowerRow77_21Degree10Chunk40 x) + (boundaryImPowerRow77_21Degree10Chunk44 x))))) := by

    dsimp only [boundaryImPowerRow77_21,boundaryImPowerRow77_21Degree10Chunk0,boundaryImPowerRow77_21Degree10Chunk4,boundaryImPowerRow77_21Degree10Chunk8,boundaryImPowerRow77_21Degree10Chunk12,boundaryImPowerRow77_21Degree10Chunk16,boundaryImPowerRow77_21Degree10Chunk20,boundaryImPowerRow77_21Degree10Chunk24,boundaryImPowerRow77_21Degree10Chunk28,boundaryImPowerRow77_21Degree10Chunk32,boundaryImPowerRow77_21Degree10Chunk36,boundaryImPowerRow77_21Degree10Chunk40,boundaryImPowerRow77_21Degree10Chunk44]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryImPowerRow77_21Degree10Chunk0Norm x).property,(boundaryImPowerRow77_21Degree10Chunk4Norm x).property,(boundaryImPowerRow77_21Degree10Chunk8Norm x).property,(boundaryImPowerRow77_21Degree10Chunk12Norm x).property,(boundaryImPowerRow77_21Degree10Chunk16Norm x).property,(boundaryImPowerRow77_21Degree10Chunk20Norm x).property,(boundaryImPowerRow77_21Degree10Chunk24Norm x).property,(boundaryImPowerRow77_21Degree10Chunk28Norm x).property,(boundaryImPowerRow77_21Degree10Chunk32Norm x).property,(boundaryImPowerRow77_21Degree10Chunk36Norm x).property,(boundaryImPowerRow77_21Degree10Chunk40Norm x).property,(boundaryImPowerRow77_21Degree10Chunk44Norm x).property]

    dsimp only [boundaryImPowerRow77_21Degree10Chunk0Norm,boundaryImPowerRow77_21Degree10Chunk4Norm,boundaryImPowerRow77_21Degree10Chunk8Norm,boundaryImPowerRow77_21Degree10Chunk12Norm,boundaryImPowerRow77_21Degree10Chunk16Norm,boundaryImPowerRow77_21Degree10Chunk20Norm,boundaryImPowerRow77_21Degree10Chunk24Norm,boundaryImPowerRow77_21Degree10Chunk28Norm,boundaryImPowerRow77_21Degree10Chunk32Norm,boundaryImPowerRow77_21Degree10Chunk36Norm,boundaryImPowerRow77_21Degree10Chunk40Norm,boundaryImPowerRow77_21Degree10Chunk44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryLowPowerRow77Degree10Chunk0 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((104096251904/531441 : ℝ)) (6-6) 1 0 10 x) + (boundaryTermPowerRow77 ((336723968/6561 : ℝ)) (6-6) 2 0 10 x)) + ((boundaryTermPowerRow77 ((-1301807104/531441 : ℝ)) (6-6) 3 0 10 x) + (boundaryTermPowerRow77 ((-1304204238848/4782969 : ℝ)) (7-6) 1 0 10 x)))

def boundaryLowPowerRow77Degree10Chunk0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryLowPowerRow77Degree10Chunk0 x=c} := by

  have he : boundaryLowPowerRow77Degree10Chunk0 x=boundaryLowPowerRow77Degree10Chunk0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryLowPowerRow77Degree10Chunk0]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryLowPowerRow77Degree10Chunk4 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((-47163277312/1594323 : ℝ)) (7-6) 2 0 10 x) + (boundaryTermPowerRow77 ((1592262656/1594323 : ℝ)) (7-6) 3 0 10 x)) + ((boundaryTermPowerRow77 ((-23604740096/4782969 : ℝ)) (8-6) 2 0 10 x) + (boundaryTermPowerRow77 ((-3967516672/1594323 : ℝ)) (8-6) 3 0 10 x)))

def boundaryLowPowerRow77Degree10Chunk4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryLowPowerRow77Degree10Chunk4 x=c} := by

  have he : boundaryLowPowerRow77Degree10Chunk4 x=boundaryLowPowerRow77Degree10Chunk4 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryLowPowerRow77Degree10Chunk4]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryLowPowerRow77Degree10Chunk8 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((692584448/1594323 : ℝ)) (8-6) 4 0 10 x) + (boundaryTermPowerRow77 ((40742912000/4782969 : ℝ)) (9-6) 3 0 10 x)) + ((boundaryTermPowerRow77 ((-4044161024/4782969 : ℝ)) (9-6) 4 0 10 x) + (boundaryTermPowerRow77 ((-51636723712/14348907 : ℝ)) (10-6) 3 0 10 x)))

def boundaryLowPowerRow77Degree10Chunk8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryLowPowerRow77Degree10Chunk8 x=c} := by

  have he : boundaryLowPowerRow77Degree10Chunk8 x=boundaryLowPowerRow77Degree10Chunk8 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryLowPowerRow77Degree10Chunk8]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryLowPowerRow77Degree10Chunk12 (x : ℕ → ℝ) : ℝ :=
  (((boundaryTermPowerRow77 ((2856648704/14348907 : ℝ)) (10-6) 4 0 10 x) + (boundaryTermPowerRow77 ((-92569600/4782969 : ℝ)) (10-6) 5 0 10 x)) + ((boundaryTermPowerRow77 ((1094238208/4782969 : ℝ)) (11-6) 4 0 10 x) + (boundaryTermPowerRow77 ((323993600/4782969 : ℝ)) (11-6) 5 0 10 x)))

def boundaryLowPowerRow77Degree10Chunk12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryLowPowerRow77Degree10Chunk12 x=c} := by

  have he : boundaryLowPowerRow77Degree10Chunk12 x=boundaryLowPowerRow77Degree10Chunk12 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryLowPowerRow77Degree10Chunk12]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryLowPowerRow77Degree10Chunk16 (x : ℕ → ℝ) : ℝ :=
  ((boundaryTermPowerRow77 ((-1133977600/14348907 : ℝ)) (12-6) 5 0 10 x) + (boundaryTermPowerRow77 ((3968921600/129140163 : ℝ)) (13-6) 5 0 10 x))

def boundaryLowPowerRow77Degree10Chunk16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryLowPowerRow77Degree10Chunk16 x=c} := by

  have he : boundaryLowPowerRow77Degree10Chunk16 x=boundaryLowPowerRow77Degree10Chunk16 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryLowPowerRow77Degree10Chunk16]

    simp (disch := omega) only [boundaryTermPowerRow77_zero_clock,boundaryTermPowerRow77_zero_above]

    norm_num [boundaryTermPowerRow77_single_sum,boundaryTermScalar77,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

    try ring_nf

  exact ⟨_,he⟩

def boundaryLowPowerRow77Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryLowPowerRow77 10 x=c} := by

  have he : boundaryLowPowerRow77 10 x=(((boundaryLowPowerRow77Degree10Chunk0 x) + (boundaryLowPowerRow77Degree10Chunk4 x)) + ((boundaryLowPowerRow77Degree10Chunk8 x) + ((boundaryLowPowerRow77Degree10Chunk12 x) + (boundaryLowPowerRow77Degree10Chunk16 x)))) := by

    dsimp only [boundaryLowPowerRow77,boundaryLowPowerRow77Degree10Chunk0,boundaryLowPowerRow77Degree10Chunk4,boundaryLowPowerRow77Degree10Chunk8,boundaryLowPowerRow77Degree10Chunk12,boundaryLowPowerRow77Degree10Chunk16]

    try ac_rfl

  conv at he =>

    rhs

    rw [(boundaryLowPowerRow77Degree10Chunk0Norm x).property,(boundaryLowPowerRow77Degree10Chunk4Norm x).property,(boundaryLowPowerRow77Degree10Chunk8Norm x).property,(boundaryLowPowerRow77Degree10Chunk12Norm x).property,(boundaryLowPowerRow77Degree10Chunk16Norm x).property]

    dsimp only [boundaryLowPowerRow77Degree10Chunk0Norm,boundaryLowPowerRow77Degree10Chunk4Norm,boundaryLowPowerRow77Degree10Chunk8Norm,boundaryLowPowerRow77Degree10Chunk12Norm,boundaryLowPowerRow77Degree10Chunk16Norm]

    try ring_nf

  exact ⟨_,he⟩

end

end HTGeometry.ThetaRatioInfinity
