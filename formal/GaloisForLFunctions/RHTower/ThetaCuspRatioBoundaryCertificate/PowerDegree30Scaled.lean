import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree30Norm

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerScaled77_30_0Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_1Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_2Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_3Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_4Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_5Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_6Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_7Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_8Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_9Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_10Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_11Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_12Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_13Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_14Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_15Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_16Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_17Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_18Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_19Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_20Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_21Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_22Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_23Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_24Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_25Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_26Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_27Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_28Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_29Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_30Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_31Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_32Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_33Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_34Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_35Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_30_36Norm : {c : ℝ // boundaryH77^30*boundaryFullPowerRow77 30 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^30*z) (boundaryFullPowerRow77Degree30Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree30Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


end

end HTGeometry.ThetaRatioInfinity
