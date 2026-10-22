import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioZeroSpeedDeterminant
/-! # Exact algebra for the zero-defect, zero-speed source-slope face. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section

def zeroSpeedFacePolynomial (k : ℝ) : ℝ := -(k ^ 8 * 49862447699362578432) + k ^ 9 * 87006854832406489202688 - k ^ 10 * 4503594714924066910765056 + k ^ 11 * 96680609196290773214035968 - k ^ 12 * 1121666574185099052365905920 + k ^ 13 * 7616263604337311010131017728 - k ^ 14 * 28810979224191826443789926400 + k ^ 15 * 22306662155762531867742437376 + k ^ 16 * 396672655873966092849871060992 - k ^ 17 * 2014738314061440598334137958400 + k ^ 18 * 1626343419808908249110610444288 + k ^ 19 * 15276291994011584740857659523072 - k ^ 20 * 47106397527293021976435546390528 + k ^ 21 * 15976187541879176187808787202048 + k ^ 22 * 416832872905227110453854989189120 - k ^ 23 * 440575117777555334891776921042944 - k ^ 24 * 1513575932900231583166800662102016 + k ^ 25 * 2733167595583519118828228195647488 + k ^ 26 * 3390638221595101491375602707464192 - k ^ 27 * 9360667124741440643774479582887936 - k ^ 28 * 8425655357616652028815256089264128 + k ^ 29 * 12182857736739815785051540212940800 + k ^ 30 * 10747360003103207275100296873771008 - k ^ 31 * 3350355996945010684212698777911296 + k ^ 32 * 1205784782784961653248270505345024 + k ^ 33 * 4880990575078758121450519929028608 + k ^ 34 * 868410389389712485210946373943296 + k ^ 35 * 120802543239921152316765867343872 + k ^ 36 * 58750963652202090470995421822976 + k ^ 37 * 11882217367861096949190085312512

theorem zeroSpeedFacePolynomial_eq (k : ℝ) (hk : (k:ℂ)≠0) :
    (zeroSpeedFacePolynomial k:ℂ)=zeroSpeedMinorPartial (k:ℂ) hk := by
  rw [(zeroSpeedMinorPartialNorm (k:ℂ) hk).property]
  dsimp only [zeroSpeedFacePolynomial,zeroSpeedMinorPartialNorm]
  push_cast
  ring

def zeroSpeedFaceShift (s : ℝ) : ℝ :=
  (4:ℝ)^37*zeroSpeedFacePolynomial ((5+s)/4)

def zeroSpeedFaceShiftNorm (s : ℝ) : {a : ℝ // zeroSpeedFaceShift s=a} := by
  have h : zeroSpeedFaceShift s=zeroSpeedFaceShift s := rfl
  conv at h =>
    rhs
    dsimp only [zeroSpeedFaceShift,zeroSpeedFacePolynomial]
    ring_nf
  exact ⟨_,h⟩


theorem zeroSpeedFaceShift_pos {s : ℝ} (hs : 0≤s) :
    0<zeroSpeedFaceShift s := by
  rw [(zeroSpeedFaceShiftNorm s).property]
  dsimp only [zeroSpeedFaceShiftNorm]
  positivity

theorem zeroSpeedFacePolynomial_pos {k : ℝ} (hk : 5/4≤k) :
    0<zeroSpeedFacePolynomial k := by
  let s := 4*k-5
  have hs : 0≤s := by dsimp [s]; linarith
  have he : (5+s)/4=k := by dsimp [s]; ring
  have hp := zeroSpeedFaceShift_pos hs
  rw [zeroSpeedFaceShift,he] at hp
  exact (mul_pos_iff_of_pos_left (by positivity : (0:ℝ)<(4:ℝ)^37)).mp hp

end
end HTGeometry.ThetaRatioSource
