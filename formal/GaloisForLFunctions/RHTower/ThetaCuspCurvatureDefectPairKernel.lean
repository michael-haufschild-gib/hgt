import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectKernel
/-!
# Coupled binary fusion for curvature-defect cooling

Retaining each theta component together with its continuous ray gives an
unconditional binary fusion inequality on the complete source domain.
The ordered-gap proof uses a positive polynomial certificate, factored
into small lemmas to respect the default Lean resource limits.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section
def rayMoment (q s : ℝ) : ℕ → ℝ
  | 2 => s^2*q^2+2*s*q+2
  | 3 => s^3*q^3+3*s^2*q^2+6*s*q+6
  | 4 => s^4*q^4+4*s^3*q^3+12*s^2*q^2+24*s*q+24
  | 5 => s^5*q^5+5*s^4*q^4+20*s^3*q^3+60*s^2*q^2+120*s*q+120
  | 6 => s^6*q^6+6*s^5*q^5+30*s^4*q^4+120*s^3*q^3+360*s^2*q^2+720*s*q+720
  | _ => 0
def doubleRayMoment (q s : ℝ) : ℕ → ℝ
  | 2 => s^2*q^2+4*s*q+6
  | 3 => s^3*q^3+6*s^2*q^2+18*s*q+24
  | 4 => s^4*q^4+8*s^3*q^3+36*s^2*q^2+96*s*q+120
  | 5 => s^5*q^5+10*s^4*q^4+60*s^3*q^3+240*s^2*q^2+600*s*q+720
  | 6 => s^6*q^6+12*s^5*q^5+90*s^4*q^4+480*s^3*q^3+1800*s^2*q^2+4320*s*q+5040
  | _ => 0
def pairMomentNumerator (q s p : ℝ) (j : ℕ) : ℝ :=
  (p+s+1)*s^j*q^(j+2)+(3*p+3/2*s)*q*rayMoment q s j+
    (9/4)*p*doubleRayMoment q s j
def pairCoolingKernel (q d e : ℝ) : ℝ :=
  12*(4*q+15)*q^4*pairMomentNumerator q (d+e) (d*e) 2+
  (-36*q*(q+3)-24*(4*q+15)*(q+3/2))*q^3*pairMomentNumerator q (d+e) (d*e) 3+
  (44*q*(q+3)*(q+3/2)+10*(4*q+15)*(q+3/2)^2)*q^2*pairMomentNumerator q (d+e) (d*e) 4+
  (-13*q*(q+3)*(q+3/2)^2-(4*q+15)*(q+3/2)^3)*q*pairMomentNumerator q (d+e) (d*e) 5+
  q*(q+3)*(q+3/2)^3*pairMomentNumerator q (d+e) (d*e) 6
def massNumerator (q d : ℝ) : ℝ := (d+1)*q+(3/2)*d
private def fusionBlock00 (y v w tail : ℝ) : ℝ :=
  NNRat.rawCast 48980771523 16 + (
    y ^ Nat.rawCast 1 * NNRat.rawCast 75934619235 16 + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * NNRat.rawCast 1183953788559 16) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 3347313088383 16)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 11689982368461 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 4445583267807 16)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 27284146711263 256)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 5418274061403 256)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 61394367231 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 12008972277 256)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * NNRat.rawCast 3347313088383 16) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 6068119604445 16)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 1769167620441 4)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 15563241910215 64)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 16641314777223 256)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 256305314097 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 83874675825 256)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * NNRat.rawCast 2022706534815 8) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 2631087213957 8)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 8515721715255 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 3250127641653 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 272038447755 16)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 31323663981 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 4 * NNRat.rawCast 2631087213957 16) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * NNRat.rawCast 4991961617775 32)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 5471964955143 64)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 81770169465 4)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 103628337795 64)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 5 * NNRat.rawCast 998392323555 16) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 666551194047 16)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 14073974856)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 25554340485 16)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock00_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock00 y v w tail := by
  unfold fusionBlock00
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock01 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 6 * NNRat.rawCast 222183731349 16) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 11793915819 2)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 14956344063 16)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 7 * Nat.rawCast 1684845117) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 344905209)) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 8 * NNRat.rawCast 344905209 4) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 1183953788559 32) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 7267054646997 64) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 7644569298831 64) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 16043886047331 256) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 9195537027123 512) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 2756113078833 1024) + (
    y ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 2646044739 16) + (
    y ^ Nat.rawCast 2 * NNRat.rawCast 323658825489 32 + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * NNRat.rawCast 9272869121133 32) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 6143566068513 8)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 79202599768809 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 57746199898773 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 172113949463625 512)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 16711470146169 256)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 372102410763 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 17979534765 128)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * NNRat.rawCast 6143566068513 8) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 41983391021481 32)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 92568141748719 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 98519908060845 128)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 51451475354397 256)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 3112658262909 128)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 125575079625 128)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * NNRat.rawCast 13994463673827 16) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 17410970924973 16)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 54129887133525 64)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock01_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock01 y v w tail := by
  unfold fusionBlock01
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock02 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 10069117932087 32)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 3307434578055 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 46897011045 16)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 4 * NNRat.rawCast 17410970924973 32) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * NNRat.rawCast 31934876669865 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 16989701082237 64)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 124377565905 2)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 155149771275 32)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 5 * NNRat.rawCast 6386975333973 32) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 2076174945045 16)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 342818948781 8)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 38259323325 8)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 6 * NNRat.rawCast 692058315015 16) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 143814843333 8)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 22392266535 8)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 7 * NNRat.rawCast 20544977619 4) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 1032767010)) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 8 * NNRat.rawCast 516383505 2) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 9272869121133 64) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 12843480767031 32) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 51213672421155 128) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 103658176101069 512) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 57786006273093 1024) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 8469711915435 1024) + (
    y ^ Nat.rawCast 2 * (w ^ Nat.rawCast 7 * NNRat.rawCast 127756467783 256) + (
    y ^ Nat.rawCast 3 * NNRat.rawCast 1121515674849 16 + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * NNRat.rawCast 3070020356847 4) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 28061429914593 16)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 20510970150267 8)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 57061347099219 32)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 41188551293169 64)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 31229698211613 256)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock02_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock02 y v w tail := by
  unfold fusionBlock02
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock03 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 341139752685 32)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 32544088713 128)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * NNRat.rawCast 28061429914593 16) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 11108364143913 4)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 92126427895593 32)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 5916113612865 4)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 96402704145057 256)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 2859436113615 64)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 227298791925 128)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * NNRat.rawCast 3702788047971 2) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 17532540398187 8)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 6528291610725 4)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 18906467904567 32)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 3042033139485 32)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 84886539489 16)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 4 * NNRat.rawCast 17532540398187 16) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * NNRat.rawCast 7752647606445 8)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 31972550010597 64)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 114501915900)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 280830843855 32)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 5 * NNRat.rawCast 1550529521289 4) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 3919824631809 16)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 315885479535 4)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 69251781465 8)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 6 * NNRat.rawCast 1306608210603 16) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 132682414095 4)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 40531410747 8)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 7 * NNRat.rawCast 18954630585 2) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 1869373242)) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 8 * NNRat.rawCast 934686621 2) + (
    y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 3070020356847 8) + (
    y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 56219922834777 64) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock03_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock03 y v w tail := by
  unfold fusionBlock03
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock04 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 13105394054325 16) + (
    y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 101841510674439 256) + (
    y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 13770690747993 128) + (
    y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 6 * NNRat.rawCast 15764887080603 1024) + (
    y ^ Nat.rawCast 3 * (w ^ Nat.rawCast 7 * NNRat.rawCast 116584278885 128) + (
    y ^ Nat.rawCast 4 * NNRat.rawCast 857542519323 4 + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * NNRat.rawCast 2755014748965 2) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 21772029315051 8)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 3608336871261)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 9556770601197 4)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 1667603082375 2)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 19716258655971 128)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 1688240309841 128)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 79419035115 256)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * NNRat.rawCast 21772029315051 8) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 63821558106531 16)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 7769433025359 2)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 61555137093639 32)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 61031612342547 128)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 14181734314323 256)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 554689083375 256)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * NNRat.rawCast 21273852702177 8) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 5982095449521 2)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 34104875509233 16)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 5998073336181 8)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 15106782970665 128)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 207153044595 32)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 4 * NNRat.rawCast 5982095449521 4) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * NNRat.rawCast 10189872358515 8)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 635396497686)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 284583407805 2)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 685326138525 64)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock04_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock04 y v w tail := by
  unfold fusionBlock04
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock05 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 5 * NNRat.rawCast 2037974471703 4) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 2500962376077 8)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 1571674605147 16)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 168998730075 16)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 6 * NNRat.rawCast 833654125359 8) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 661007700171 16)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 98910913185 16)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 7 * NNRat.rawCast 94429671453 8) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 2280964455)) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 8 * NNRat.rawCast 2280964455 4) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * NNRat.rawCast 2755014748965 4) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 20970334026027 16) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 36459537237999 32) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 33909295617387 64) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 5 * NNRat.rawCast 8880569582391 64) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 6 * NNRat.rawCast 4955107798431 256) + (
    y ^ Nat.rawCast 4 * (w ^ Nat.rawCast 7 * NNRat.rawCast 574056013761 512) + (
    y ^ Nat.rawCast 5 * NNRat.rawCast 714706217793 2 + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * Nat.rawCast 1714333398093) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 11996205170967 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 7262367690213 2)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 36618917465043 16)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 12342693081249 16)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 8876774310705 64)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 46486935423 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 68950447857 256)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * NNRat.rawCast 11996205170967 4) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 16356938121837 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 59947568886807 16)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 14293300293531 8)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 27558320941665 64)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 3131323599321 64)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock05_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock05 y v w tail := by
  unfold fusionBlock05
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock06 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 481572971325 256)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * NNRat.rawCast 5452312707279 2) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 5832162855441 2)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 7952042044737 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 2714590141335 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 3340126860075 32)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 179847251721 32)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 4 * NNRat.rawCast 5832162855441 4) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 1195353230085)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 1152893550915 2)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 503881421085 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 594990157095 64)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 5 * Nat.rawCast 478141292034) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 1138190437395 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 348183287991 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 146722232385 16)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 6 * NNRat.rawCast 379396812465 4) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 146630719557 4)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 85873012083 16)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 7 * NNRat.rawCast 20947245651 2) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 1980300069)) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 8 * NNRat.rawCast 1980300069 4) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 1714333398093 2) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 11173676066019 8) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 9072422673147 8) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 4 * NNRat.rawCast 16143505566255 32) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 5 * NNRat.rawCast 4088869664319 32) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 6 * NNRat.rawCast 2220768616257 128) + (
    y ^ Nat.rawCast 5 * (w ^ Nat.rawCast 7 * NNRat.rawCast 125771306013 128) + (
    y ^ Nat.rawCast 6 * Nat.rawCast 378804639204 + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * Nat.rawCast 1516689367290) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 2404147317318)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock06_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock06 y v w tail := by
  unfold fusionBlock06
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock07 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 5363534441385 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 6442225466697 4)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 1047884557509 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 732658380795 8)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 29999772279 4)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 10950219333 64)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * Nat.rawCast 2404147317318) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 6140682913365 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 10614711698397 4)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 1218259588473)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 2281451573529 8)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 1012877913681 32)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 76479991425 64)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * Nat.rawCast 2046894304455) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 2086243115850)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 1361021070222)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 901024001343 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 1081968441075 16)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 28562060349 8)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 4 * Nat.rawCast 1043121557925) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 823272016860)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 1534161026223 4)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 163393383465 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 94492101555 16)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 5 * Nat.rawCast 329308806744) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 189941107464)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 113015694123 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 23301380565 4)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 6 * Nat.rawCast 63313702488) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 47658340737 2)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 13637740527 4)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 7 * Nat.rawCast 6808334391) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock07_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock07 y v w tail := by
  unfold fusionBlock07
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock08 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 1257988644)) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 8 * Nat.rawCast 314497161) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 758344683645) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 4355786542581 4) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 3 * NNRat.rawCast 1658320068465 2) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 4 * NNRat.rawCast 1411612940007 4) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 5 * NNRat.rawCast 345481100775 4) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 6 * NNRat.rawCast 729681036903 64) + (
    y ^ Nat.rawCast 6 * (w ^ Nat.rawCast 7 * NNRat.rawCast 40347365949 64) + (
    y ^ Nat.rawCast 7 * Nat.rawCast 273861681372 + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * Nat.rawCast 969143002992) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 1417226521914)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 1469070080379)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 1683958476501 2)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * Nat.rawCast 264301874235)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 358978905783 8)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 57399493401 16)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 2575684575 32)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * Nat.rawCast 1417226521914) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 1706559657102)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 2791471242033 2)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 616936542255)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 1121298999039 8)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 121437436977 8)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 17989441875 32)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * Nat.rawCast 1137706438068) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 1107512765532)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 691915631490)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 221941725624)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 129914741295 4)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 6718299975 4)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 4 * Nat.rawCast 553756382766) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock08_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock08 y v w tail := by
  unfold fusionBlock08
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock09 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 420936904980)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 189375118587)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 78560892765 2)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 22226207625 8)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 5 * Nat.rawCast 168374761992) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 94085106930)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 27196374591)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 5480895375 2)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 6 * Nat.rawCast 31361702310) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 11484196038)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 3207836925 2)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 7 * Nat.rawCast 3281198868) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 591802200)) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 8 * Nat.rawCast 147950550) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 484571501496) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 2 * Nat.rawCast 627391879506) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 3 * NNRat.rawCast 900216861345 2) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 4 * NNRat.rawCast 733744407357 4) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 5 * Nat.rawCast 43359410241) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 6 * NNRat.rawCast 44469242757 8) + (
    y ^ Nat.rawCast 7 * (w ^ Nat.rawCast 7 * NNRat.rawCast 9590481243 32) + (
    y ^ Nat.rawCast 8 * Nat.rawCast 139004752212 + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * Nat.rawCast 449116925292) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 614045003292)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 596063405610)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * Nat.rawCast 326641612743)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 395779271571 4)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 65221515063 4)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 2542764879 2)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 448499511 16)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * Nat.rawCast 614045003292) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 701286814980)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock09_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock09 y v w tail := by
  unfold fusionBlock09
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock10 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * Nat.rawCast 544519547271)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 231834271680)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 204362794827 4)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 21576470337 4)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 3132470475 16)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * Nat.rawCast 467524543320) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 435755869056)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 260977982940)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 81090544014)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 23118258195 2)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 1169845983 2)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 4 * Nat.rawCast 217877934528) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 159632702730)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 69345032337)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 13995264240)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 3870211185 4)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 5 * Nat.rawCast 63853081092) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 34559712396)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 9699482052)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * Nat.rawCast 954378855)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 6 * Nat.rawCast 11519904132) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 4101376356)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * Nat.rawCast 558575109)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 7 * Nat.rawCast 1171821816) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 206098992)) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 8 * Nat.rawCast 51524748) + (
    y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 1 * Nat.rawCast 224558462646) + (
    y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 2 * Nat.rawCast 266745412773) + (
    y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 3 * Nat.rawCast 181150566975) + (
    y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 4 * NNRat.rawCast 283096941039 4) + (
    y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 5 * NNRat.rawCast 129235630059 8) + (
    y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 6 * NNRat.rawCast 32154408891 16) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock10_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock10 y v w tail := by
  unfold fusionBlock10
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock11 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 8 * (w ^ Nat.rawCast 7 * NNRat.rawCast 844228899 8) + (
    y ^ Nat.rawCast 9 * Nat.rawCast 49703615496 + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * Nat.rawCast 149566178304) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 193093912104)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 176702167404)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * Nat.rawCast 92771473572)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * Nat.rawCast 27127469370)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 8674590141 2)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 1318287447 4)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * Nat.rawCast 7135290)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * Nat.rawCast 193093912104) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 210213956664)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * Nat.rawCast 155454168828)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 63794298288)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 27265831497 2)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 2804318469 2)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * Nat.rawCast 49835250)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * Nat.rawCast 140142637776) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 125365390512)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 72067174272)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 21688329348)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * Nat.rawCast 3009435795)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * Nat.rawCast 148890960)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 4 * Nat.rawCast 62682695256) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 44306463120)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 18586884654)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 3647746710)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * Nat.rawCast 246288600)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 5 * Nat.rawCast 17722585248) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 9291263976)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 2530603188)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * Nat.rawCast 242935200)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock11_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock11 y v w tail := by
  unfold fusionBlock11
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock12 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 6 * Nat.rawCast 3097087992) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 1071504504)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * Nat.rawCast 142184160)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 7 * Nat.rawCast 306144144) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 52462080)) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 8 * Nat.rawCast 13115520) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 1 * Nat.rawCast 74783089152) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 2 * Nat.rawCast 82579371558) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 3 * Nat.rawCast 53315424258) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 4 * NNRat.rawCast 39995013819 2) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 5 * Nat.rawCast 4408233741) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 6 * NNRat.rawCast 4254732117 8) + (
    y ^ Nat.rawCast 9 * (w ^ Nat.rawCast 7 * NNRat.rawCast 217378161 8) + (
    y ^ Nat.rawCast 10 * Nat.rawCast 12279625272 + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * Nat.rawCast 34867453752) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 42826218048)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 37158263604)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * Nat.rawCast 18729231096)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 10579732575 2)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * Nat.rawCast 820442325)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * Nat.rawCast 60716322)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 5160159 4)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * Nat.rawCast 42826218048) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 44633510640)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * Nat.rawCast 31532546304)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 12483444774)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * Nat.rawCast 2586793221)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 518091327 2)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 36040275 4)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * Nat.rawCast 29755673760) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 25606630416)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 14149049196)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock12_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock12 y v w tail := by
  unfold fusionBlock12
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock13 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 4124640048)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * Nat.rawCast 556870365)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * Nat.rawCast 26919054)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 4 * Nat.rawCast 12803315208) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 8740129020)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 3542165664)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 675737640)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * Nat.rawCast 44528265)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 5 * Nat.rawCast 3496051608) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 1775814768)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 469250568)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * Nat.rawCast 43921980)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 6 * Nat.rawCast 591938256) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 198955512)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * Nat.rawCast 25706484)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 7 * Nat.rawCast 56844432) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 9484992)) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 8 * Nat.rawCast 2371248) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 1 * Nat.rawCast 17433726876) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 2 * Nat.rawCast 18078644772) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 3 * Nat.rawCast 11140213362) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 4 * NNRat.rawCast 8035659579 2) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 5 * NNRat.rawCast 3422786595 4) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 6 * NNRat.rawCast 200177757 2) + (
    y ^ Nat.rawCast 10 * (w ^ Nat.rawCast 7 * NNRat.rawCast 19885743 4) + (
    y ^ Nat.rawCast 11 * Nat.rawCast 1995076656 + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * Nat.rawCast 5394610368) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 6341033808)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 5242726512)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * Nat.rawCast 2542333440)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * Nat.rawCast 694139220)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * Nat.rawCast 104443557)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock13_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock13 y v w tail := by
  unfold fusionBlock13
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock14 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * Nat.rawCast 7525071)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 313677 2)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * Nat.rawCast 6341033808) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 6350171040)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * Nat.rawCast 4298625648)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 1643501232)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * Nat.rawCast 330300369)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * Nat.rawCast 32196726)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 2190825 2)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * Nat.rawCast 4233447360) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 3512584416)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 1868535648)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 527823432)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * Nat.rawCast 69323220)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * Nat.rawCast 3272724)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 4 * Nat.rawCast 1756292208) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 1159302240)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 454186236)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 84213720)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * Nat.rawCast 5413590)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 5 * Nat.rawCast 463720896) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 228329424)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 58536720)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * Nat.rawCast 5339880)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 6 * Nat.rawCast 76109808) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 24851232)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * Nat.rawCast 3125304)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 7 * Nat.rawCast 7100352) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 1153152)) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 8 * Nat.rawCast 288288) + (
    y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 1 * Nat.rawCast 2697305184) + (
    y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 2 * Nat.rawCast 2648002428) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock14_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock14 y v w tail := by
  unfold fusionBlock14
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock15 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 3 * Nat.rawCast 1563001416) + (
    y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 4 * Nat.rawCast 542972661) + (
    y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 5 * Nat.rawCast 111796146) + (
    y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 6 * NNRat.rawCast 50708589 4) + (
    y ^ Nat.rawCast 11 * (w ^ Nat.rawCast 7 * NNRat.rawCast 1223685 2) + (
    y ^ Nat.rawCast 12 * Nat.rawCast 191538432 + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * Nat.rawCast 496601280) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 561338208)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 444260160)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * Nat.rawCast 207719760)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * Nat.rawCast 54884540)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * Nat.rawCast 8014590)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * Nat.rawCast 562142)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * Nat.rawCast 11490)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * Nat.rawCast 561338208) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 541976400)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * Nat.rawCast 352567440)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 130350440)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * Nat.rawCast 25420110)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * Nat.rawCast 2411953)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * Nat.rawCast 80250)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * Nat.rawCast 361317600) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 289695360)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 148620400)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 40707200)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * Nat.rawCast 5201350)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * Nat.rawCast 239760)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 4 * Nat.rawCast 144847680) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 92580160)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 35094000)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 6325440)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * Nat.rawCast 396600)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock15_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock15 y v w tail := by
  unfold fusionBlock15
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock16 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 5 * Nat.rawCast 37032064) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 17688480)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 4400912)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * Nat.rawCast 391200)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 6 * Nat.rawCast 5896160) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 1870736)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * Nat.rawCast 228960)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 7 * Nat.rawCast 534496) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 84480)) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 8 * Nat.rawCast 21120) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 1 * Nat.rawCast 248300640) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 2 * Nat.rawCast 232320096) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 3 * Nat.rawCast 131800680) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 4 * Nat.rawCast 44184480) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 5 * Nat.rawCast 8803202) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 6 * Nat.rawCast 968006) + (
    y ^ Nat.rawCast 12 * (w ^ Nat.rawCast 7 * NNRat.rawCast 90771 2) + (
    y ^ Nat.rawCast 13 * Nat.rawCast 8211456 + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * Nat.rawCast 20528640) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * Nat.rawCast 22410432)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * Nat.rawCast 17050176)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * Nat.rawCast 7704720)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * Nat.rawCast 1972800)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * Nat.rawCast 279780)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * Nat.rawCast 19108)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * Nat.rawCast 383)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * Nat.rawCast 22410432) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * Nat.rawCast 20927808)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * Nat.rawCast 13122000)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * Nat.rawCast 4698720)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * Nat.rawCast 889860)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * Nat.rawCast 82212)) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock16_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock16 y v w tail := by
  unfold fusionBlock16
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock17 (y v w tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * Nat.rawCast 2675)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * Nat.rawCast 13951872) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * Nat.rawCast 10834560)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * Nat.rawCast 5371200)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * Nat.rawCast 1427840)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * Nat.rawCast 177560)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * Nat.rawCast 7992)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 4 * Nat.rawCast 5417280) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * Nat.rawCast 3358080)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * Nat.rawCast 1233120)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * Nat.rawCast 216160)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * Nat.rawCast 13220)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 5 * Nat.rawCast 1343232) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * Nat.rawCast 623040)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * Nat.rawCast 150528)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * Nat.rawCast 13040)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 6 * Nat.rawCast 207680) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * Nat.rawCast 64064)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * Nat.rawCast 7632)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 7 * Nat.rawCast 18304) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 2816)) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 8 * Nat.rawCast 704) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 1 * Nat.rawCast 10264320) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 2 * Nat.rawCast 9206784) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 3 * Nat.rawCast 5037120) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 4 * Nat.rawCast 1632960) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 5 * Nat.rawCast 315216) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 6 * Nat.rawCast 33632) + (
    y ^ Nat.rawCast 13 * (w ^ Nat.rawCast 7 * Nat.rawCast 1532) + (
    v ^ Nat.rawCast 1 * NNRat.rawCast 185491758753 16 + (
    v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 1 * NNRat.rawCast 889356232413 32) + (
    v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 2 * NNRat.rawCast 6412553051301 128) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock17_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock17 y v w tail := by
  unfold fusionBlock17
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock18 (_y v w tail : ℝ) : ℝ :=
  v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 3 * NNRat.rawCast 2520930595869 64) + (
    v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 4 * NNRat.rawCast 7936374143457 512) + (
    v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 5 * NNRat.rawCast 804264208965 256) + (
    v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 6 * NNRat.rawCast 37048346433 128) + (
    v ^ Nat.rawCast 1 * (w ^ Nat.rawCast 7 * NNRat.rawCast 1831877127 256) + (
    v ^ Nat.rawCast 2 * NNRat.rawCast 889356232413 32 + (
    v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 1 * NNRat.rawCast 3271098894003 64) + (
    v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 2 * NNRat.rawCast 3986897485491 64) + (
    v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 3 * NNRat.rawCast 4512583215657 128) + (
    v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 4 * NNRat.rawCast 2464679337489 256) + (
    v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 5 * NNRat.rawCast 308807079075 256) + (
    v ^ Nat.rawCast 2 * (w ^ Nat.rawCast 6 * NNRat.rawCast 12794442075 256) + (
    v ^ Nat.rawCast 3 * NNRat.rawCast 1090366298001 32 + (
    v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 1 * NNRat.rawCast 732983444811 16) + (
    v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 2 * NNRat.rawCast 2459329498089 64) + (
    v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 3 * NNRat.rawCast 480448704609 32) + (
    v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 4 * NNRat.rawCast 327423457305 128) + (
    v ^ Nat.rawCast 3 * (w ^ Nat.rawCast 5 * NNRat.rawCast 4778186031 32) + (
    v ^ Nat.rawCast 4 * NNRat.rawCast 732983444811 32 + (
    v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 1 * NNRat.rawCast 1432702639305 64) + (
    v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 2 * NNRat.rawCast 807173316999 64) + (
    v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 3 * NNRat.rawCast 6146115165 2) + (
    v ^ Nat.rawCast 4 * (w ^ Nat.rawCast 4 * NNRat.rawCast 15807712545 64) + (
    v ^ Nat.rawCast 5 * NNRat.rawCast 286540527861 32 + (
    v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 1 * NNRat.rawCast 98017383717 16) + (
    v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 2 * NNRat.rawCast 33822499563 16) + (
    v ^ Nat.rawCast 5 * (w ^ Nat.rawCast 3 * NNRat.rawCast 3898119735 16) + (
    v ^ Nat.rawCast 6 * NNRat.rawCast 32672461239 16 + (
    v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 1 * NNRat.rawCast 14154931035 16) + (
    v ^ Nat.rawCast 6 * (w ^ Nat.rawCast 2 * NNRat.rawCast 2281476213 16) + (
    v ^ Nat.rawCast 7 * NNRat.rawCast 2022133005 8 + (
    v ^ Nat.rawCast 7 * (w ^ Nat.rawCast 1 * Nat.rawCast 52612659) + (
    tail))))))))))))))))))))))))))))))))
private theorem fusionBlock18_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock18 y v w tail := by
  unfold fusionBlock18
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private def fusionBlock19 (_y v w tail : ℝ) : ℝ :=
  v ^ Nat.rawCast 8 * NNRat.rawCast 52612659 4 + (
    w ^ Nat.rawCast 1 * NNRat.rawCast 185491758753 32 + (
    w ^ Nat.rawCast 2 * NNRat.rawCast 1961600005215 128 + (
    w ^ Nat.rawCast 3 * NNRat.rawCast 4231820455299 256 + (
    w ^ Nat.rawCast 4 * NNRat.rawCast 4568793494031 512 + (
    w ^ Nat.rawCast 5 * NNRat.rawCast 2683704596877 1024 + (
    w ^ Nat.rawCast 6 * NNRat.rawCast 410445170325 1024 + (
    w ^ Nat.rawCast 7 * NNRat.rawCast 12823139889 512 + (
    tail))))))))
private theorem fusionBlock19_nonneg (y v w tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (_hw : 0 ≤ w) (ht : 0 ≤ tail) :
    0 ≤ fusionBlock19 y v w tail := by
  unfold fusionBlock19
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2,
    Mathlib.Tactic.RingNF.nnrat_rawCast, pow_one]
  positivity
private theorem pairCoolingKernel_fusion_shift (y v w : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ 384*(3/2+y)*((3+v)*normalizedDefectCoolingKernel (3/2+y) (3+v)*massNumerator (3/2+y) (3+v+w)+
      (3+v+w)*normalizedDefectCoolingKernel (3/2+y) (3+v+w)*massNumerator (3/2+y) (3+v))-
      pairCoolingKernel (3/2+y) (3+v) (3+v+w) := by
  simp only [pairCoolingKernel, pairMomentNumerator, rayMoment, doubleRayMoment, massNumerator]
  unfold normalizedDefectCoolingKernel momentNumeratorTwo momentNumeratorThree momentNumeratorFour
    momentNumeratorFive momentNumeratorSix
  norm_num only [Nat.reduceAdd]
  ring_nf (config := {mode := .raw})
  apply fusionBlock00_nonneg y v w _ hy hv hw
  apply fusionBlock01_nonneg y v w _ hy hv hw
  apply fusionBlock02_nonneg y v w _ hy hv hw
  apply fusionBlock03_nonneg y v w _ hy hv hw
  apply fusionBlock04_nonneg y v w _ hy hv hw
  apply fusionBlock05_nonneg y v w _ hy hv hw
  apply fusionBlock06_nonneg y v w _ hy hv hw
  apply fusionBlock07_nonneg y v w _ hy hv hw
  apply fusionBlock08_nonneg y v w _ hy hv hw
  apply fusionBlock09_nonneg y v w _ hy hv hw
  apply fusionBlock10_nonneg y v w _ hy hv hw
  apply fusionBlock11_nonneg y v w _ hy hv hw
  apply fusionBlock12_nonneg y v w _ hy hv hw
  apply fusionBlock13_nonneg y v w _ hy hv hw
  apply fusionBlock14_nonneg y v w _ hy hv hw
  apply fusionBlock15_nonneg y v w _ hy hv hw
  apply fusionBlock16_nonneg y v w _ hy hv hw
  apply fusionBlock17_nonneg y v w _ hy hv hw
  apply fusionBlock18_nonneg y v w _ hy hv hw
  apply fusionBlock19_nonneg y v w _ hy hv hw
  exact le_rfl
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section
private theorem pairCoolingKernel_fusion_ordered {q d e : ℝ}
    (hq : 3/2 ≤ q) (hd : 3 ≤ d) (hde : d ≤ e) :
    pairCoolingKernel q d e ≤
      384*q*(d*normalizedDefectCoolingKernel q d*massNumerator q e+
        e*normalizedDefectCoolingKernel q e*massNumerator q d) := by
  have h := pairCoolingKernel_fusion_shift (q-3/2) (d-3) (e-d)
    (by linarith) (by linarith) (by linarith)
  have hq' : 3/2+(q-3/2)=q := by ring
  have hd' : 3+(d-3)=d := by ring
  have he' : d+(e-d)=e := by ring
  exact sub_nonneg.mp (by simpa only [hq',hd',he'] using h)

theorem pairCoolingKernel_fusion {q d e : ℝ}
    (hq : 3/2 ≤ q) (hd : 3 ≤ d) (he : 3 ≤ e) :
    pairCoolingKernel q d e ≤
      384*q*(d*normalizedDefectCoolingKernel q d*massNumerator q e+
        e*normalizedDefectCoolingKernel q e*massNumerator q d) := by
  rcases le_total d e with hde | hed
  · exact pairCoolingKernel_fusion_ordered hq hd hde
  · have hs : pairCoolingKernel q d e = pairCoolingKernel q e d := by
      simp only [pairCoolingKernel,add_comm d e,mul_comm d e]
    calc
      pairCoolingKernel q d e = pairCoolingKernel q e d := hs
      _ ≤ 384*q*(e*normalizedDefectCoolingKernel q e*massNumerator q d+
          d*normalizedDefectCoolingKernel q d*massNumerator q e) :=
        pairCoolingKernel_fusion_ordered hq he hed
      _ = _ := by ring
end
end RHTower.ThetaCuspDefect
