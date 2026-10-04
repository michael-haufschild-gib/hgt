import GaloisForLFunctions.RHTower.ThetaCuspRatioZeroSpeedSlice
/-! # Exact algebra for the zero-defect, zero-speed source-slope face. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def zeroDefectPoly2Part0 : Poly := (((1152) + ((-(X Coord.K : Poly) * 1620) + (-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 1) * 12))) + (((-(X Coord.K : Poly) ^ 2 * 31104) + ((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 1) * 576)) + ((-(X Coord.K : Poly) ^ 3 * 3888) + (-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 1) * 3024))))

def zeroDefectPoly2 : Poly := zeroDefectPoly2Part0

theorem zeroDefectPoly2_eq (u k : ℂ) :
    eval (slicePoint u k) (integerReflection 2)=
      eval (slicePoint (u^2) k) zeroDefectPoly2 := by
  rw [(sliceValue2 u k).property]
  dsimp only [sliceValue2,zeroDefectPoly2,zeroDefectPoly2Part0]
  simp [slicePoint] <;> ring

theorem zeroDefectPoly2_partial (u k : ℂ) :
    eval (slicePoint u k) (pderiv Coord.U (integerReflection 2))=
      2*u*eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectPoly2) := by
  rw [reflectionBalanced2_eq,reflectionClean2_eq]
  simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,zeroDefectPoly2,zeroDefectPoly2Part0,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
  ring

def zeroSpeedValue2 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^2*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly2=a} := by
  have h : k^2*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly2=k^2*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly2 := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly2,zeroDefectPoly2Part0,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroSpeedPartial2 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^2*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly2)=a} := by
  have h : k^2*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly2)=k^2*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly2) := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly2,zeroDefectPoly2Part0,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroDefectPoly4Part0 : Poly := ((((819072) + ((X Coord.K : Poly) * 20481984)) + ((-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 1) * 312768) + (((X Coord.K : Poly) ^ 2 * 70368912) + (-(X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 1) * 609120)))) + ((((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 2) * 23760) + ((X Coord.K : Poly) ^ 3 * 25894080)) + (((X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 1) * 10435392) + ((-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 2) * 165888) + ((X Coord.K : Poly) ^ 4 * 11337408)))))

def zeroDefectPoly4Part1 : Poly := ((((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 1) * 1399680) + ((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 2) * 451008)) + (((X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 1) * 1679616) + ((-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 2) * 186624) + (((X Coord.U : Poly) ^ 1) * 93312))))

def zeroDefectPoly4 : Poly := (zeroDefectPoly4Part0 + zeroDefectPoly4Part1)

theorem zeroDefectPoly4_eq (u k : ℂ) :
    eval (slicePoint u k) (integerReflection 4)=
      eval (slicePoint (u^2) k) zeroDefectPoly4 := by
  rw [(sliceValue4 u k).property]
  dsimp only [sliceValue4,zeroDefectPoly4,zeroDefectPoly4Part0,zeroDefectPoly4Part1]
  simp [slicePoint] <;> ring

theorem zeroDefectPoly4_partial (u k : ℂ) :
    eval (slicePoint u k) (pderiv Coord.U (integerReflection 4))=
      2*u*eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectPoly4) := by
  rw [reflectionBalanced4_eq,reflectionClean4_eq]
  simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,zeroDefectPoly4,zeroDefectPoly4Part0,zeroDefectPoly4Part1,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
  ring

def zeroSpeedValue4 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^4*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly4=a} := by
  have h : k^4*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly4=k^4*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly4 := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly4,zeroDefectPoly4Part0,zeroDefectPoly4Part1,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroSpeedPartial4 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^4*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly4)=a} := by
  have h : k^4*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly4)=k^4*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly4) := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly4,zeroDefectPoly4Part0,zeroDefectPoly4Part1,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroDefectPoly6Part0 : Poly := ((((-8338360320) + (-(X Coord.K : Poly) * 90870584832)) + (((X Coord.K : Poly) * ((X Coord.U : Poly) ^ 1) * 1239681024) + ((-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 2) * 54120960) + (-(X Coord.K : Poly) ^ 2 * 262125911808)))) + (((-(X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 1) * 5641643520) + ((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 2) * 110419200)) + (((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 3) * 1492992) + ((-(X Coord.K : Poly) ^ 3 * 203900763456) + (-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 1) * 47910346560)))))

def zeroDefectPoly6Part1 : Poly := (((((X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 2) * 1067535936) + (-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 3) * 18035136)) + ((-(X Coord.K : Poly) ^ 4 * 122353307136) + ((-(X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 1) * 15444069120) + (-(X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 2) * 4425228288)))) + ((((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 3) * 93747456) + ((X Coord.K : Poly) ^ 5 * 952342272)) + ((-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 1) * 23657391360) + (((X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 2) * 915390720) + (-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 3) * 151352064)))))

def zeroDefectPoly6Part2 : Poly := (((-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 1) * 3083774976) + ((-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 2) * 604661760) + ((X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 3) * 69424128))) + ((((X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 2) * 241864704) + (-(X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 3) * 26873856)) + ((-((X Coord.U : Poly) ^ 1) * 167712768) + (((X Coord.U : Poly) ^ 2) * 5971968))))

def zeroDefectPoly6 : Poly := (zeroDefectPoly6Part0 + (zeroDefectPoly6Part1 + zeroDefectPoly6Part2))

theorem zeroDefectPoly6_eq (u k : ℂ) :
    eval (slicePoint u k) (integerReflection 6)=
      eval (slicePoint (u^2) k) zeroDefectPoly6 := by
  rw [(sliceValue6 u k).property]
  dsimp only [sliceValue6,zeroDefectPoly6,zeroDefectPoly6Part0,zeroDefectPoly6Part1,zeroDefectPoly6Part2]
  simp [slicePoint] <;> ring

theorem zeroDefectPoly6_partial (u k : ℂ) :
    eval (slicePoint u k) (pderiv Coord.U (integerReflection 6))=
      2*u*eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectPoly6) := by
  rw [reflectionBalanced6_eq,reflectionClean6_eq]
  simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,zeroDefectPoly6,zeroDefectPoly6Part0,zeroDefectPoly6Part1,zeroDefectPoly6Part2,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
  ring

def zeroSpeedValue6 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^6*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly6=a} := by
  have h : k^6*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly6=k^6*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly6 := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly6,zeroDefectPoly6Part0,zeroDefectPoly6Part1,zeroDefectPoly6Part2,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroSpeedPartial6 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^6*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly6)=a} := by
  have h : k^6*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly6)=k^6*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly6) := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly6,zeroDefectPoly6Part0,zeroDefectPoly6Part1,zeroDefectPoly6Part2,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroDefectPoly8Part0 : Poly := ((((48721763450880) + ((X Coord.K : Poly) * 465200636755968)) + ((-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 1) * 5043506135040) + (((X Coord.K : Poly) * ((X Coord.U : Poly) ^ 2) * 280455561216) + (-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 3) * 6975258624)))) + ((((X Coord.K : Poly) ^ 2 * 1390654809612288) + ((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 1) * 60218694660096)) + ((-(X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 2) * 1816099356672) + (((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 3) * 37381533696) + ((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 4) * 95551488)))))

def zeroDefectPoly8Part1 : Poly := (((((X Coord.K : Poly) ^ 3 * 1594560904169472) + ((X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 1) * 304304294430720)) + ((-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 2) * 3709196789760) + (((X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 3) * 12712826880) + (-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 4) * 2030469120)))) + ((((X Coord.K : Poly) ^ 4 * 1043671487738112) + ((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 1) * 267216539010048)) + (((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 2) * 30406152273408) + ((-(X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 3) * 1095470189568) + ((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 4) * 17800632576)))))

def zeroDefectPoly8Part2 : Poly := (((((X Coord.K : Poly) ^ 5 * 1258724385792) + ((X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 1) * 320229714622464)) + ((-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 2) * 8830480343040) + (((X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 3) * 3199829723136) + (-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 4) * 75026580480)))) + ((((X Coord.K : Poly) ^ 6 * 25140203394048) + (-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 1) * 1704420569088)) + (((X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 2) * 34018391549952) + ((-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 3) * 2749759819776) + ((X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 4) * 139464115200)))))

def zeroDefectPoly8Part3 : Poly := (((((X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 1) * 33892500971520) + (-(X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 2) * 7144199626752)) + (((X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 3) * 1306553131008) + ((-(X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 4) * 64765992960) + (-(X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 2) * 914248581120)))) + (((-(X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 3) * 110290305024) + ((X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 4) * 18381717504)) + (((X Coord.K : Poly) ^ 9 * ((X Coord.U : Poly) ^ 3) * 34828517376) + ((-(X Coord.K : Poly) ^ 9 * ((X Coord.U : Poly) ^ 4) * 3869835264) + (-((X Coord.U : Poly) ^ 1) * 293964152832)))))

def zeroDefectPoly8Part4 : Poly := ((-((X Coord.U : Poly) ^ 2) * 37786632192) + (((X Coord.U : Poly) ^ 3) * 382205952))

def zeroDefectPoly8 : Poly := ((zeroDefectPoly8Part0 + zeroDefectPoly8Part1) + (zeroDefectPoly8Part2 + (zeroDefectPoly8Part3 + zeroDefectPoly8Part4)))

theorem zeroDefectPoly8_eq (u k : ℂ) :
    eval (slicePoint u k) (integerReflection 8)=
      eval (slicePoint (u^2) k) zeroDefectPoly8 := by
  rw [(sliceValue8 u k).property]
  dsimp only [sliceValue8,zeroDefectPoly8,zeroDefectPoly8Part0,zeroDefectPoly8Part1,zeroDefectPoly8Part2,zeroDefectPoly8Part3,zeroDefectPoly8Part4]
  simp [slicePoint] <;> ring

theorem zeroDefectPoly8_partial (u k : ℂ) :
    eval (slicePoint u k) (pderiv Coord.U (integerReflection 8))=
      2*u*eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectPoly8) := by
  rw [reflectionBalanced8_eq,reflectionClean8_eq]
  simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,zeroDefectPoly8,zeroDefectPoly8Part0,zeroDefectPoly8Part1,zeroDefectPoly8Part2,zeroDefectPoly8Part3,zeroDefectPoly8Part4,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
  ring

def zeroSpeedValue8 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^8*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly8=a} := by
  have h : k^8*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly8=k^8*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly8 := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly8,zeroDefectPoly8Part0,zeroDefectPoly8Part1,zeroDefectPoly8Part2,zeroDefectPoly8Part3,zeroDefectPoly8Part4,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroSpeedPartial8 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^8*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly8)=a} := by
  have h : k^8*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly8)=k^8*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly8) := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly8,zeroDefectPoly8Part0,zeroDefectPoly8Part1,zeroDefectPoly8Part2,zeroDefectPoly8Part3,zeroDefectPoly8Part4,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroDefectPoly10Part0 : Poly := ((((-312165555505201152) + (-(X Coord.K : Poly) * 2936102282906370048)) + (((X Coord.K : Poly) * ((X Coord.U : Poly) ^ 1) * 61684770355347456) + ((-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 2) * 197242493534208) + ((X Coord.K : Poly) * ((X Coord.U : Poly) ^ 3) * 80341172158464)))) + (((-(X Coord.K : Poly) * ((X Coord.U : Poly) ^ 4) * 762883080192) + (-(X Coord.K : Poly) ^ 2 * 9455534033560731648)) + ((-(X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 1) * 412258829129220096) + (((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 2) * 19009199682551808) + (-(X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 3) * 403853428260864)))))

def zeroDefectPoly10Part1 : Poly := (((((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 4) * 7818213851136) + ((X Coord.K : Poly) ^ 2 * ((X Coord.U : Poly) ^ 5) * 6115295232)) + ((-(X Coord.K : Poly) ^ 3 * 13150464920064589824) + ((-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 1) * 2447771852650954752) + ((X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 2) * 20716788679262208)))) + ((((X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 3) * 1256456716075008) + (-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 4) * 27614129209344)) + ((-(X Coord.K : Poly) ^ 3 * ((X Coord.U : Poly) ^ 5) * 209066655744) + ((-(X Coord.K : Poly) ^ 4 * 8554127497378209792) + (-(X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 1) * 3961660559120695296)))))

def zeroDefectPoly10Part2 : Poly := ((((-(X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 2) * 173128209213800448) + ((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 3) * 5898464181780480)) + ((-(X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 4) * 87926724108288) + (((X Coord.K : Poly) ^ 4 * ((X Coord.U : Poly) ^ 5) * 2911629017088) + ((X Coord.K : Poly) ^ 5 * 677116232091085824)))) + (((-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 1) * 4382336574963588096) + (-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 2) * 28115931239221248)) + ((-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 3) * 30272545686878208) + (((X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 4) * 1220349372668928) + (-(X Coord.K : Poly) ^ 5 * ((X Coord.U : Poly) ^ 5) * 21649604520960)))))

def zeroDefectPoly10Part3 : Poly := (((((X Coord.K : Poly) ^ 6 * 328311602422530048) + (-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 1) * 294241410708922368)) + ((-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 2) * 613251565613383680) + (((X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 3) * 53149080840781824) + (-(X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 4) * 4460464678846464)))) + ((((X Coord.K : Poly) ^ 6 * ((X Coord.U : Poly) ^ 5) * 91471564873728) + ((X Coord.K : Poly) ^ 7 * 383949003059269632)) + ((-(X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 1) * 1288727614526312448) + (((X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 2) * 374568440387198976) + (-(X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 3) * 88589516401631232)))))

def zeroDefectPoly10Part4 : Poly := (((((X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 4) * 6618583363719168) + (-(X Coord.K : Poly) ^ 7 * ((X Coord.U : Poly) ^ 5) * 213164635115520)) + (((X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 1) * 53484012180504576) + ((-(X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 2) * 182663105027899392) + ((X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 3) * 51833819612971008)))) + (((-(X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 4) * 5853234192187392) + ((X Coord.K : Poly) ^ 8 * ((X Coord.U : Poly) ^ 5) * 217846571433984)) + (((X Coord.K : Poly) ^ 9 * ((X Coord.U : Poly) ^ 2) * 32705127157137408) + ((-(X Coord.K : Poly) ^ 9 * ((X Coord.U : Poly) ^ 3) * 8910632371027968) + ((X Coord.K : Poly) ^ 9 * ((X Coord.U : Poly) ^ 4) * 1133703069106176)))))

def zeroDefectPoly10Part5 : Poly := ((((-(X Coord.K : Poly) ^ 9 * ((X Coord.U : Poly) ^ 5) * 51534596210688) + (-(X Coord.K : Poly) ^ 10 * ((X Coord.U : Poly) ^ 3) * 229450272473088)) + ((-(X Coord.K : Poly) ^ 10 * ((X Coord.U : Poly) ^ 4) * 19225341591552) + (((X Coord.K : Poly) ^ 10 * ((X Coord.U : Poly) ^ 5) * 4225860108288) + ((X Coord.K : Poly) ^ 11 * ((X Coord.U : Poly) ^ 4) * 5015306502144)))) + (((-(X Coord.K : Poly) ^ 11 * ((X Coord.U : Poly) ^ 5) * 557256278016) + (((X Coord.U : Poly) ^ 1) * 10648022001647616)) + ((((X Coord.U : Poly) ^ 2) * 332976678764544) + ((-((X Coord.U : Poly) ^ 3) * 5278009393152) + (((X Coord.U : Poly) ^ 4) * 24461180928)))))

def zeroDefectPoly10 : Poly := ((zeroDefectPoly10Part0 + (zeroDefectPoly10Part1 + zeroDefectPoly10Part2)) + (zeroDefectPoly10Part3 + (zeroDefectPoly10Part4 + zeroDefectPoly10Part5)))

theorem zeroDefectPoly10_eq (u k : ℂ) :
    eval (slicePoint u k) (integerReflection 10)=
      eval (slicePoint (u^2) k) zeroDefectPoly10 := by
  rw [(sliceValue10 u k).property]
  dsimp only [sliceValue10,zeroDefectPoly10,zeroDefectPoly10Part0,zeroDefectPoly10Part1,zeroDefectPoly10Part2,zeroDefectPoly10Part3,zeroDefectPoly10Part4,zeroDefectPoly10Part5]
  simp [slicePoint] <;> ring

theorem zeroDefectPoly10_partial (u k : ℂ) :
    eval (slicePoint u k) (pderiv Coord.U (integerReflection 10))=
      2*u*eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectPoly10) := by
  rw [reflectionBalanced10_eq,reflectionClean10_eq]
  simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,zeroDefectPoly10,zeroDefectPoly10Part0,zeroDefectPoly10Part1,zeroDefectPoly10Part2,zeroDefectPoly10Part3,zeroDefectPoly10Part4,zeroDefectPoly10Part5,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
  ring

def zeroSpeedValue10 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^10*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly10=a} := by
  have h : k^10*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly10=k^10*eval (slicePoint (9-6/k-4/k^2) k) zeroDefectPoly10 := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly10,zeroDefectPoly10Part0,zeroDefectPoly10Part1,zeroDefectPoly10Part2,zeroDefectPoly10Part3,zeroDefectPoly10Part4,zeroDefectPoly10Part5,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroSpeedPartial10 (k : ℂ) (hk : k≠0) :
    {a : ℂ // k^10*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly10)=a} := by
  have h : k^10*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly10)=k^10*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectPoly10) := rfl
  conv at h =>
    rhs
    simp [zeroDefectPoly10,zeroDefectPoly10Part0,zeroDefectPoly10Part1,zeroDefectPoly10Part2,zeroDefectPoly10Part3,zeroDefectPoly10Part4,zeroDefectPoly10Part5,slicePoint,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    field_simp [hk]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def zeroDefectMinor : Poly :=
  -zeroDefectPoly2*zeroDefectPoly6*zeroDefectPoly10+
  zeroDefectPoly2*zeroDefectPoly8^2+zeroDefectPoly4^2*zeroDefectPoly10-
  2*zeroDefectPoly4*zeroDefectPoly6*zeroDefectPoly8+zeroDefectPoly6^3


@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

private theorem minor_reflection_model : integerThirdMinor =
    -(integerReflection 2)*(integerReflection 6)*(integerReflection 10)+
    (integerReflection 2)*(integerReflection 8)^2+
    (integerReflection 4)^2*(integerReflection 10)-
    2*(integerReflection 4)*(integerReflection 6)*(integerReflection 8)+
    (integerReflection 6)^3 := by
  norm_num [integerThirdMinor,integerSignedMoment]
  ring

theorem zeroDefectMinor_eq (u k : ℂ) :
    eval (slicePoint u k) integerThirdMinor=
      eval (slicePoint (u^2) k) zeroDefectMinor := by
  rw [minor_reflection_model]
  simp only [map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,
    zeroDefectPoly2_eq,zeroDefectPoly4_eq,zeroDefectPoly6_eq,
    zeroDefectPoly8_eq,zeroDefectPoly10_eq,zeroDefectMinor]

theorem zeroDefectMinor_partial (u k : ℂ) :
    eval (slicePoint u k) (pderiv Coord.U integerThirdMinor)=
      2*u*eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectMinor) := by
  rw [minor_reflection_model]
  simp only [zeroDefectMinor,map_add,map_sub,pderiv_mul,pderiv_pow,map_neg,
    pd_ofNat,zero_mul,zero_add,map_mul,map_pow,map_ofNat,map_natCast,
    zeroDefectPoly2_eq,zeroDefectPoly4_eq,zeroDefectPoly6_eq,
    zeroDefectPoly8_eq,zeroDefectPoly10_eq,
    zeroDefectPoly2_partial,zeroDefectPoly4_partial,zeroDefectPoly6_partial,
    zeroDefectPoly8_partial,zeroDefectPoly10_partial]
  ring

/-- The source flow crosses the zero-speed face; this is a transverse partial,
not the derivative of the determinant restricted to that face. -/
theorem thirdSlope_zeroSpeed_slice (u k : ℂ)
    (hf : k^2*(9-u^2)-6*k-4=0) :
    eval (slicePoint u k) integerThirdSlope =
      2*u*(6*k-1)*(6*k*(9-u^2))*
        eval (slicePoint (u^2) k) (pderiv Coord.U zeroDefectMinor) := by
  rw [integerSlope_zeroSpeed u k hf,zeroDefectMinor_partial]
  ring

end
end HTGeometry.ThetaRatioSource
