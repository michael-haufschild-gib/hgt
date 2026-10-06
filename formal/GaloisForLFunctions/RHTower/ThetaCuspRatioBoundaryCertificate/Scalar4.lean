import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment4
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryMoment4ReValue75Part0 (v k : ℂ) : ℂ :=
  ((((((79/2592 : ℂ)) + (k ^ 1 * (439/576 : ℂ))) + ((k ^ 1 * (v ^ 1 * (-3671/124416 : ℂ))) + (k ^ 1 * (v ^ 2 * (-1151/186624 : ℂ))))) + (((k ^ 1 * (v ^ 3 * (1897/10077696 : ℂ))) + (k ^ 2 * (2011/768 : ℂ))) + ((k ^ 2 * (v ^ 1 * (725/13824 : ℂ))) + (k ^ 2 * (v ^ 2 * (-8855/559872 : ℂ)))))) + ((((k ^ 2 * (v ^ 3 * (-2515/10077696 : ℂ))) + (k ^ 2 * (v ^ 4 * (-49/45349632 : ℂ)))) + ((k ^ 3 * (185/192 : ℂ)) + (k ^ 3 * (v ^ 1 * (2419/6912 : ℂ))))) + (((k ^ 3 * (v ^ 2 * (7637/186624 : ℂ))) + (k ^ 3 * (v ^ 3 * (-7375/5038848 : ℂ)))) + ((k ^ 3 * (v ^ 4 * (-7/5038848 : ℂ))) + (k ^ 4 * (27/64 : ℂ))))))

def boundaryMoment4ReValue75Part1 (v k : ℂ) : ℂ :=
  ((((k ^ 4 * (v ^ 1 * (73/1152 : ℂ))) + (k ^ 4 * (v ^ 2 * (-121/5832 : ℂ)))) + ((k ^ 4 * (v ^ 3 * (2165/839808 : ℂ))) + ((k ^ 4 * (v ^ 4 * (1/209952 : ℂ))) + (k ^ 5 * (v ^ 1 * (11/192 : ℂ)))))) + (((k ^ 5 * (v ^ 2 * (55/15552 : ℂ))) + ((k ^ 5 * (v ^ 3 * (-151/139968 : ℂ))) + (k ^ 5 * (v ^ 4 * (-1/419904 : ℂ))))) + ((v ^ 1 * (-193/15552 : ℂ)) + ((v ^ 2 * (287/139968 : ℂ)) + (0)))))

def boundaryMoment4ReValue75 (v k : ℂ) : ℂ :=
  ((boundaryMoment4ReValue75Part0 v k) + (boundaryMoment4ReValue75Part1 v k))

theorem boundaryMoment4ReValue75_eq (v k : ℂ) :
    (boundaryMoment4ReNorm v k).val=boundaryMoment4ReValue75 v k := by
  dsimp only [boundaryMoment4ReNorm,boundaryMoment4ReValue75,boundaryMoment4ReValue75Part0,boundaryMoment4ReValue75Part1]
  norm_num
  all_goals ring

def boundaryMoment4ImValue75Part0 (v k : ℂ) : ℂ :=
  ((((k ^ 1 * (v ^ 1 * (-19/1728 : ℂ))) + ((k ^ 1 * (v ^ 2 * (41/2592 : ℂ))) + (k ^ 1 * (v ^ 3 * (119/419904 : ℂ))))) + (((k ^ 2 * (v ^ 1 * (-1805/1728 : ℂ))) + (k ^ 2 * (v ^ 2 * (635/7776 : ℂ)))) + ((k ^ 2 * (v ^ 3 * (101/419904 : ℂ))) + (k ^ 3 * (v ^ 1 * (-19/144 : ℂ)))))) + ((((k ^ 3 * (v ^ 2 * (-1027/5832 : ℂ))) + (k ^ 3 * (v ^ 3 * (-53/34992 : ℂ)))) + ((k ^ 4 * (v ^ 1 * (-7/48 : ℂ))) + (k ^ 4 * (v ^ 2 * (143/1944 : ℂ))))) + (((k ^ 4 * (v ^ 3 * (11/11664 : ℂ))) + (v ^ 1 * (425/3888 : ℂ))) + ((v ^ 2 * (-131/11664 : ℂ)) + (0)))))

def boundaryMoment4ImValue75 (v k : ℂ) : ℂ :=
  (boundaryMoment4ImValue75Part0 v k)

theorem boundaryMoment4ImValue75_eq (v k : ℂ) :
    (boundaryMoment4ImNorm v k).val=boundaryMoment4ImValue75 v k := by
  dsimp only [boundaryMoment4ImNorm,boundaryMoment4ImValue75,boundaryMoment4ImValue75Part0]
  norm_num
  all_goals ring

def boundaryFlow4ReValue75Part0 (v k : ℂ) : ℂ :=
  (((((k ^ 1 * (v ^ 1 * (158/27 : ℂ))) + (k ^ 1 * (v ^ 2 * (-667/15552 : ℂ)))) + ((k ^ 1 * (v ^ 3 * (-31225/209952 : ℂ))) + (k ^ 1 * (v ^ 4 * (4417/1259712 : ℂ))))) + (((k ^ 2 * (v ^ 1 * (274/9 : ℂ))) + (k ^ 2 * (v ^ 2 * (11519/3888 : ℂ)))) + ((k ^ 2 * (v ^ 3 * (-82475/279936 : ℂ))) + (k ^ 2 * (v ^ 4 * (-2459/419904 : ℂ)))))) + ((((k ^ 2 * (v ^ 5 * (-49/839808 : ℂ))) + (k ^ 3 * (v ^ 1 * (2021/96 : ℂ)))) + ((k ^ 3 * (v ^ 2 * (2071/5184 : ℂ))) + (k ^ 3 * (v ^ 3 * (335227/279936 : ℂ))))) + (((k ^ 3 * (v ^ 4 * (-17641/629856 : ℂ))) + (k ^ 3 * (v ^ 5 * (-917/22674816 : ℂ)))) + ((k ^ 4 * (v ^ 1 * (3/2 : ℂ))) + (k ^ 4 * (v ^ 2 * (685/864 : ℂ)))))))

def boundaryFlow4ReValue75Part1 (v k : ℂ) : ℂ :=
  (((((k ^ 4 * (v ^ 3 * (-4625/5832 : ℂ))) + (k ^ 4 * (v ^ 4 * (36089/629856 : ℂ)))) + ((k ^ 4 * (v ^ 5 * (95/314928 : ℂ))) + (k ^ 5 * (v ^ 1 * (9/8 : ℂ))))) + (((k ^ 5 * (v ^ 2 * (-49/72 : ℂ))) + (k ^ 5 * (v ^ 3 * (2089/23328 : ℂ)))) + ((k ^ 5 * (v ^ 4 * (-2107/104976 : ℂ))) + (k ^ 5 * (v ^ 5 * (-59/209952 : ℂ)))))) + ((((k ^ 6 * (v ^ 2 * (5/6 : ℂ))) + (k ^ 6 * (v ^ 3 * (-23/486 : ℂ)))) + ((k ^ 6 * (v ^ 4 * (-25/4374 : ℂ))) + (k ^ 6 * (v ^ 5 * (1/13122 : ℂ))))) + (((v ^ 1 * (-109/324 : ℂ)) + (v ^ 2 * (-2447/5832 : ℂ))) + ((v ^ 3 * (739/17496 : ℂ)) + (0)))))

def boundaryFlow4ReValue75 (v k : ℂ) : ℂ :=
  ((boundaryFlow4ReValue75Part0 v k) + (boundaryFlow4ReValue75Part1 v k))

theorem boundaryFlow4ReValue75_eq (v k : ℂ) :
    (boundaryFlow4ReNorm v k).val=boundaryFlow4ReValue75 v k := by
  dsimp only [boundaryFlow4ReNorm,boundaryFlow4ReValue75,boundaryFlow4ReValue75Part0,boundaryFlow4ReValue75Part1]
  norm_num
  all_goals ring

def boundaryFlow4ImValue75Part0 (v k : ℂ) : ℂ :=
  (((((k ^ 1 * (v ^ 1 * (-7/288 : ℂ))) + (k ^ 1 * (v ^ 2 * (-5885/31104 : ℂ)))) + ((k ^ 1 * (v ^ 3 * (1297/5184 : ℂ))) + (k ^ 1 * (v ^ 4 * (7721/839808 : ℂ))))) + (((k ^ 2 * (v ^ 1 * (4273/96 : ℂ))) + (k ^ 2 * (v ^ 2 * (-260539/10368 : ℂ)))) + ((k ^ 2 * (v ^ 3 * (8759/5832 : ℂ))) + (k ^ 2 * (v ^ 4 * (2657/839808 : ℂ)))))) + ((((k ^ 2 * (v ^ 5 * (-49/3779136 : ℂ))) + (k ^ 3 * (v ^ 1 * (541/16 : ℂ)))) + ((k ^ 3 * (v ^ 2 * (5783/1728 : ℂ))) + (k ^ 3 * (v ^ 3 * (-142373/46656 : ℂ))))) + (((k ^ 3 * (v ^ 4 * (-7975/139968 : ℂ))) + (k ^ 3 * (v ^ 5 * (-7/419904 : ℂ)))) + ((k ^ 4 * (v ^ 1 * 9)) + (k ^ 4 * (v ^ 2 * (2273/288 : ℂ)))))))

def boundaryFlow4ImValue75Part1 (v k : ℂ) : ℂ :=
  ((((k ^ 4 * (v ^ 3 * (9341/11664 : ℂ))) + (k ^ 4 * (v ^ 4 * (1097/23328 : ℂ)))) + ((k ^ 4 * (v ^ 5 * (1/17496 : ℂ))) + ((k ^ 5 * (v ^ 2 * (-23/48 : ℂ))) + (k ^ 5 * (v ^ 3 * (2453/3888 : ℂ)))))) + (((k ^ 5 * (v ^ 4 * (-7/1296 : ℂ))) + ((k ^ 5 * (v ^ 5 * (-1/34992 : ℂ))) + (v ^ 1 * (-61/16 : ℂ)))) + ((v ^ 2 * (5353/1944 : ℂ)) + ((v ^ 3 * (-2377/11664 : ℂ)) + (0)))))

def boundaryFlow4ImValue75 (v k : ℂ) : ℂ :=
  ((boundaryFlow4ImValue75Part0 v k) + (boundaryFlow4ImValue75Part1 v k))

theorem boundaryFlow4ImValue75_eq (v k : ℂ) :
    (boundaryFlow4ImNorm v k).val=boundaryFlow4ImValue75 v k := by
  dsimp only [boundaryFlow4ImNorm,boundaryFlow4ImValue75,boundaryFlow4ImValue75Part0,boundaryFlow4ImValue75Part1]
  norm_num
  all_goals ring

end
end HTGeometry.ThetaRatioInfinity
