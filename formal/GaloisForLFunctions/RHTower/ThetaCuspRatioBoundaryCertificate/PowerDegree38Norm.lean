import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree38Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree38Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x))=c} := by

  have he : ((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x))=(boundaryRePowerRow77_0Degree38Norm x).val+(boundaryRePowerRow77_1Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree38Norm x).property (boundaryRePowerRow77_1Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree38Norm,boundaryRePowerRow77_1Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x))=c} := by

  have he : ((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x))=(boundaryRePowerRow77_3Degree38Norm x).val+(boundaryRePowerRow77_4Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree38Norm x).property (boundaryRePowerRow77_4Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree38Norm,boundaryRePowerRow77_4Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x))))=(boundaryRePowerRow77_2Degree38Norm x).val+(boundaryFullPowerDegree38Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree38Norm x).property (boundaryFullPowerDegree38Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree38Norm,boundaryFullPowerDegree38Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x))))))=(boundaryFullPowerDegree38Block0Norm x).val+(boundaryFullPowerDegree38Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block0Norm x).property (boundaryFullPowerDegree38Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block0Norm,boundaryFullPowerDegree38Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x))=c} := by

  have he : ((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x))=(boundaryRePowerRow77_6Degree38Norm x).val+(boundaryRePowerRow77_7Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree38Norm x).property (boundaryRePowerRow77_7Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree38Norm,boundaryRePowerRow77_7Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x))))=(boundaryRePowerRow77_5Degree38Norm x).val+(boundaryFullPowerDegree38Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree38Norm x).property (boundaryFullPowerDegree38Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree38Norm,boundaryFullPowerDegree38Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))=c} := by

  have he : ((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))=(boundaryRePowerRow77_9Degree38Norm x).val+(boundaryRePowerRow77_10Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree38Norm x).property (boundaryRePowerRow77_10Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree38Norm,boundaryRePowerRow77_10Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))))=(boundaryRePowerRow77_8Degree38Norm x).val+(boundaryFullPowerDegree38Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree38Norm x).property (boundaryFullPowerDegree38Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree38Norm,boundaryFullPowerDegree38Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))))))=(boundaryFullPowerDegree38Block5Norm x).val+(boundaryFullPowerDegree38Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block5Norm x).property (boundaryFullPowerDegree38Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block5Norm,boundaryFullPowerDegree38Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x))))))))=(boundaryFullPowerDegree38Block3Norm x).val+(boundaryFullPowerDegree38Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block3Norm x).property (boundaryFullPowerDegree38Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block3Norm,boundaryFullPowerDegree38Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x))=c} := by

  have he : ((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x))=(boundaryRePowerRow77_12Degree38Norm x).val+(boundaryRePowerRow77_13Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree38Norm x).property (boundaryRePowerRow77_13Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree38Norm,boundaryRePowerRow77_13Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x))))=(boundaryRePowerRow77_11Degree38Norm x).val+(boundaryFullPowerDegree38Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree38Norm x).property (boundaryFullPowerDegree38Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree38Norm,boundaryFullPowerDegree38Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x))=c} := by

  have he : ((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x))=(boundaryRePowerRow77_15Degree38Norm x).val+(boundaryRePowerRow77_16Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree38Norm x).property (boundaryRePowerRow77_16Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree38Norm,boundaryRePowerRow77_16Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x))))=(boundaryRePowerRow77_14Degree38Norm x).val+(boundaryFullPowerDegree38Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree38Norm x).property (boundaryFullPowerDegree38Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree38Norm,boundaryFullPowerDegree38Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x))))))=(boundaryFullPowerDegree38Block11Norm x).val+(boundaryFullPowerDegree38Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block11Norm x).property (boundaryFullPowerDegree38Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block11Norm,boundaryFullPowerDegree38Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x))=c} := by

  have he : ((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x))=(boundaryRePowerRow77_18Degree38Norm x).val+(boundaryRePowerRow77_19Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree38Norm x).property (boundaryRePowerRow77_19Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree38Norm,boundaryRePowerRow77_19Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x))))=(boundaryRePowerRow77_17Degree38Norm x).val+(boundaryFullPowerDegree38Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree38Norm x).property (boundaryFullPowerDegree38Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree38Norm,boundaryFullPowerDegree38Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))=c} := by

  have he : ((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))=(boundaryRePowerRow77_21Degree38Norm x).val+(boundaryRePowerRow77_22Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree38Norm x).property (boundaryRePowerRow77_22Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree38Norm,boundaryRePowerRow77_22Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))=(boundaryRePowerRow77_20Degree38Norm x).val+(boundaryFullPowerDegree38Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree38Norm x).property (boundaryFullPowerDegree38Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree38Norm,boundaryFullPowerDegree38Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))))=(boundaryFullPowerDegree38Block16Norm x).val+(boundaryFullPowerDegree38Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block16Norm x).property (boundaryFullPowerDegree38Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block16Norm,boundaryFullPowerDegree38Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))))))=(boundaryFullPowerDegree38Block14Norm x).val+(boundaryFullPowerDegree38Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block14Norm x).property (boundaryFullPowerDegree38Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block14Norm,boundaryFullPowerDegree38Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x)))))))))+(((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x)))))))))+(((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x))))))))))=(boundaryFullPowerDegree38Block9Norm x).val+(boundaryFullPowerDegree38Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block9Norm x).property (boundaryFullPowerDegree38Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block9Norm,boundaryFullPowerDegree38Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x))=c} := by

  have he : ((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x))=(boundaryImPowerRow77_0Degree38Norm x).val+(boundaryImPowerRow77_1Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree38Norm x).property (boundaryImPowerRow77_1Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree38Norm,boundaryImPowerRow77_1Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x))=c} := by

  have he : ((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x))=(boundaryImPowerRow77_3Degree38Norm x).val+(boundaryImPowerRow77_4Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree38Norm x).property (boundaryImPowerRow77_4Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree38Norm,boundaryImPowerRow77_4Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x))))=(boundaryImPowerRow77_2Degree38Norm x).val+(boundaryFullPowerDegree38Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree38Norm x).property (boundaryFullPowerDegree38Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree38Norm,boundaryFullPowerDegree38Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x))))))=(boundaryFullPowerDegree38Block22Norm x).val+(boundaryFullPowerDegree38Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block22Norm x).property (boundaryFullPowerDegree38Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block22Norm,boundaryFullPowerDegree38Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x))=c} := by

  have he : ((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x))=(boundaryImPowerRow77_6Degree38Norm x).val+(boundaryImPowerRow77_7Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree38Norm x).property (boundaryImPowerRow77_7Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree38Norm,boundaryImPowerRow77_7Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x))))=(boundaryImPowerRow77_5Degree38Norm x).val+(boundaryFullPowerDegree38Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree38Norm x).property (boundaryFullPowerDegree38Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree38Norm,boundaryFullPowerDegree38Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))=c} := by

  have he : ((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))=(boundaryImPowerRow77_9Degree38Norm x).val+(boundaryImPowerRow77_10Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree38Norm x).property (boundaryImPowerRow77_10Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree38Norm,boundaryImPowerRow77_10Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))))=(boundaryImPowerRow77_8Degree38Norm x).val+(boundaryFullPowerDegree38Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree38Norm x).property (boundaryFullPowerDegree38Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree38Norm,boundaryFullPowerDegree38Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))))))=(boundaryFullPowerDegree38Block27Norm x).val+(boundaryFullPowerDegree38Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block27Norm x).property (boundaryFullPowerDegree38Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block27Norm,boundaryFullPowerDegree38Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x))))))))=(boundaryFullPowerDegree38Block25Norm x).val+(boundaryFullPowerDegree38Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block25Norm x).property (boundaryFullPowerDegree38Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block25Norm,boundaryFullPowerDegree38Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x))=c} := by

  have he : ((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x))=(boundaryImPowerRow77_12Degree38Norm x).val+(boundaryImPowerRow77_13Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree38Norm x).property (boundaryImPowerRow77_13Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree38Norm,boundaryImPowerRow77_13Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x))))=(boundaryImPowerRow77_11Degree38Norm x).val+(boundaryFullPowerDegree38Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree38Norm x).property (boundaryFullPowerDegree38Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree38Norm,boundaryFullPowerDegree38Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x))=c} := by

  have he : ((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x))=(boundaryImPowerRow77_15Degree38Norm x).val+(boundaryImPowerRow77_16Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree38Norm x).property (boundaryImPowerRow77_16Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree38Norm,boundaryImPowerRow77_16Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x))))=(boundaryImPowerRow77_14Degree38Norm x).val+(boundaryFullPowerDegree38Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree38Norm x).property (boundaryFullPowerDegree38Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree38Norm,boundaryFullPowerDegree38Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x))))))=(boundaryFullPowerDegree38Block33Norm x).val+(boundaryFullPowerDegree38Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block33Norm x).property (boundaryFullPowerDegree38Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block33Norm,boundaryFullPowerDegree38Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x))=c} := by

  have he : ((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x))=(boundaryImPowerRow77_18Degree38Norm x).val+(boundaryImPowerRow77_19Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree38Norm x).property (boundaryImPowerRow77_19Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree38Norm,boundaryImPowerRow77_19Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x))))=(boundaryImPowerRow77_17Degree38Norm x).val+(boundaryFullPowerDegree38Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree38Norm x).property (boundaryFullPowerDegree38Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree38Norm,boundaryFullPowerDegree38Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))=c} := by

  have he : ((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))=(boundaryImPowerRow77_21Degree38Norm x).val+(boundaryLowPowerRow77Degree38Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree38Norm x).property (boundaryLowPowerRow77Degree38Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree38Norm,boundaryLowPowerRow77Degree38Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))=(boundaryImPowerRow77_20Degree38Norm x).val+(boundaryFullPowerDegree38Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree38Norm x).property (boundaryFullPowerDegree38Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree38Norm,boundaryFullPowerDegree38Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))=(boundaryFullPowerDegree38Block38Norm x).val+(boundaryFullPowerDegree38Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block38Norm x).property (boundaryFullPowerDegree38Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block38Norm,boundaryFullPowerDegree38Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))))=(boundaryFullPowerDegree38Block36Norm x).val+(boundaryFullPowerDegree38Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block36Norm x).property (boundaryFullPowerDegree38Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block36Norm,boundaryFullPowerDegree38Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x)))))))))+(((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x)))))))))+(((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))))))=(boundaryFullPowerDegree38Block31Norm x).val+(boundaryFullPowerDegree38Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block31Norm x).property (boundaryFullPowerDegree38Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block31Norm,boundaryFullPowerDegree38Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree38Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x)))))))))+(((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x)))))))))))+(((((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x)))))))))+(((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x)))))))))+(((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x)))))))))))+(((((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x)))))))))+(((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x))))))))))))=(boundaryFullPowerDegree38Block21Norm x).val+(boundaryFullPowerDegree38Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree38Block21Norm x).property (boundaryFullPowerDegree38Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block21Norm,boundaryFullPowerDegree38Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree38Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 38 x=c} := by

  have he0 : boundaryFullPowerRow77 38 x=((((((((((boundaryRePowerRow77_0 38 x)+(boundaryRePowerRow77_1 38 x)))+(((boundaryRePowerRow77_2 38 x)+(((boundaryRePowerRow77_3 38 x)+(boundaryRePowerRow77_4 38 x)))))))+(((((boundaryRePowerRow77_5 38 x)+(((boundaryRePowerRow77_6 38 x)+(boundaryRePowerRow77_7 38 x)))))+(((boundaryRePowerRow77_8 38 x)+(((boundaryRePowerRow77_9 38 x)+(boundaryRePowerRow77_10 38 x)))))))))+(((((((boundaryRePowerRow77_11 38 x)+(((boundaryRePowerRow77_12 38 x)+(boundaryRePowerRow77_13 38 x)))))+(((boundaryRePowerRow77_14 38 x)+(((boundaryRePowerRow77_15 38 x)+(boundaryRePowerRow77_16 38 x)))))))+(((((boundaryRePowerRow77_17 38 x)+(((boundaryRePowerRow77_18 38 x)+(boundaryRePowerRow77_19 38 x)))))+(((boundaryRePowerRow77_20 38 x)+(((boundaryRePowerRow77_21 38 x)+(boundaryRePowerRow77_22 38 x)))))))))))+(((((((((boundaryImPowerRow77_0 38 x)+(boundaryImPowerRow77_1 38 x)))+(((boundaryImPowerRow77_2 38 x)+(((boundaryImPowerRow77_3 38 x)+(boundaryImPowerRow77_4 38 x)))))))+(((((boundaryImPowerRow77_5 38 x)+(((boundaryImPowerRow77_6 38 x)+(boundaryImPowerRow77_7 38 x)))))+(((boundaryImPowerRow77_8 38 x)+(((boundaryImPowerRow77_9 38 x)+(boundaryImPowerRow77_10 38 x)))))))))+(((((((boundaryImPowerRow77_11 38 x)+(((boundaryImPowerRow77_12 38 x)+(boundaryImPowerRow77_13 38 x)))))+(((boundaryImPowerRow77_14 38 x)+(((boundaryImPowerRow77_15 38 x)+(boundaryImPowerRow77_16 38 x)))))))+(((((boundaryImPowerRow77_17 38 x)+(((boundaryImPowerRow77_18 38 x)+(boundaryImPowerRow77_19 38 x)))))+(((boundaryImPowerRow77_20 38 x)+(((boundaryImPowerRow77_21 38 x)+(boundaryLowPowerRow77 38 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree38Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree38Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
