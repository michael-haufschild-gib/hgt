import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment2
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryMoment2ReValue75Part0 (v k : ℂ) : ℂ :=
  (((((1/27 : ℂ)) + ((k ^ 1 * (-5/96 : ℂ)) + (k ^ 1 * (v ^ 1 * (17/2592 : ℂ))))) + ((k ^ 1 * (v ^ 2 * (7/11664 : ℂ))) + ((k ^ 2 * (-1 : ℂ)) + (k ^ 2 * (v ^ 1 * (-5/432 : ℂ)))))) + (((k ^ 2 * (v ^ 2 * (5/3888 : ℂ))) + ((k ^ 3 * (-1/8 : ℂ)) + (k ^ 3 * (v ^ 1 * (-1/12 : ℂ))))) + ((k ^ 3 * (v ^ 2 * (-1/648 : ℂ))) + ((v ^ 1 * (1/162 : ℂ)) + (0)))))

def boundaryMoment2ReValue75 (v k : ℂ) : ℂ :=
  (boundaryMoment2ReValue75Part0 v k)

theorem boundaryMoment2ReValue75_eq (v k : ℂ) :
    (boundaryMoment2ReNorm v k).val=boundaryMoment2ReValue75 v k := by
  dsimp only [boundaryMoment2ReNorm,boundaryMoment2ReValue75,boundaryMoment2ReValue75Part0]
  norm_num
  all_goals ring

def boundaryMoment2ImValue75Part0 (v k : ℂ) : ℂ :=
  (((k ^ 1 * (v ^ 1 * (-5/108 : ℂ))) + (k ^ 2 * (v ^ 1 * (1/3 : ℂ)))) + ((v ^ 1 * (-17/324 : ℂ)) + (0)))

def boundaryMoment2ImValue75 (v k : ℂ) : ℂ :=
  (boundaryMoment2ImValue75Part0 v k)

theorem boundaryMoment2ImValue75_eq (v k : ℂ) :
    (boundaryMoment2ImNorm v k).val=boundaryMoment2ImValue75 v k := by
  dsimp only [boundaryMoment2ImNorm,boundaryMoment2ImValue75,boundaryMoment2ImValue75Part0]
  norm_num
  all_goals ring

def boundaryFlow2ReValue75Part0 (v k : ℂ) : ℂ :=
  ((((k ^ 1 * (v ^ 1 * (-5/9 : ℂ))) + ((k ^ 1 * (v ^ 2 * (13/648 : ℂ))) + (k ^ 1 * (v ^ 3 * (217/17496 : ℂ))))) + (((k ^ 2 * (v ^ 1 * (-221/24 : ℂ))) + (k ^ 2 * (v ^ 2 * (-215/324 : ℂ)))) + ((k ^ 2 * (v ^ 3 * (85/5832 : ℂ))) + (k ^ 3 * (v ^ 1 * (-11/2 : ℂ)))))) + ((((k ^ 3 * (v ^ 2 * (7/18 : ℂ))) + (k ^ 3 * (v ^ 3 * (-14/243 : ℂ)))) + ((k ^ 4 * (v ^ 1 * (9/2 : ℂ))) + (k ^ 4 * (v ^ 2 * (-7/9 : ℂ))))) + (((k ^ 4 * (v ^ 3 * (5/162 : ℂ))) + (v ^ 1 * (10/27 : ℂ))) + ((v ^ 2 * (31/243 : ℂ)) + (0)))))

def boundaryFlow2ReValue75 (v k : ℂ) : ℂ :=
  (boundaryFlow2ReValue75Part0 v k)

theorem boundaryFlow2ReValue75_eq (v k : ℂ) :
    (boundaryFlow2ReNorm v k).val=boundaryFlow2ReValue75 v k := by
  dsimp only [boundaryFlow2ReNorm,boundaryFlow2ReValue75,boundaryFlow2ReValue75Part0]
  norm_num
  all_goals ring

def boundaryFlow2ImValue75Part0 (v k : ℂ) : ℂ :=
  ((((k ^ 1 * (v ^ 1 * (61/24 : ℂ))) + ((k ^ 1 * (v ^ 2 * (-433/648 : ℂ))) + (k ^ 1 * (v ^ 3 * (7/972 : ℂ))))) + ((k ^ 2 * (v ^ 1 * (-17 : ℂ))) + ((k ^ 2 * (v ^ 2 * (61/12 : ℂ))) + (k ^ 2 * (v ^ 3 * (5/324 : ℂ)))))) + (((k ^ 3 * (v ^ 1 * (-15/2 : ℂ))) + ((k ^ 3 * (v ^ 2 * (-7/9 : ℂ))) + (k ^ 3 * (v ^ 3 * (-1/54 : ℂ))))) + ((v ^ 1 * (59/24 : ℂ)) + ((v ^ 2 * (-529/648 : ℂ)) + (0)))))

def boundaryFlow2ImValue75 (v k : ℂ) : ℂ :=
  (boundaryFlow2ImValue75Part0 v k)

theorem boundaryFlow2ImValue75_eq (v k : ℂ) :
    (boundaryFlow2ImNorm v k).val=boundaryFlow2ImValue75 v k := by
  dsimp only [boundaryFlow2ImNorm,boundaryFlow2ImValue75,boundaryFlow2ImValue75Part0]
  norm_num
  all_goals ring

end
end HTGeometry.ThetaRatioInfinity
