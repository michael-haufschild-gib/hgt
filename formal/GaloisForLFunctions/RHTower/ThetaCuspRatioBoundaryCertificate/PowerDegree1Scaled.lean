import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree1Norm

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerScaled77_1_0Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_1Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_2Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_3Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_4Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_5Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_6Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_7Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_8Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_9Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_10Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_11Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_12Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_13Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_14Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_15Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_16Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_17Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_18Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_19Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_20Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_21Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_22Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_23Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_24Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_25Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_26Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_27Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_28Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_29Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_30Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_31Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_32Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_33Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_34Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_35Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


def boundaryFullPowerScaled77_1_36Norm : {c : ℝ // boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)=c} := by

  have he := congrArg (fun z : ℝ => boundaryH77^1*z) (boundaryFullPowerRow77Degree1Norm (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77Degree1Norm]

    norm_num [boundaryH77,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩


end

end HTGeometry.ThetaRatioInfinity
