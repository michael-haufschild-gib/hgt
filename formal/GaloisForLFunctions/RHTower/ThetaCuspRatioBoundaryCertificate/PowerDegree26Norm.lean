import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree26Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree26Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x))=c} := by

  have he : ((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x))=(boundaryRePowerRow77_0Degree26Norm x).val+(boundaryRePowerRow77_1Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree26Norm x).property (boundaryRePowerRow77_1Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree26Norm,boundaryRePowerRow77_1Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x))=c} := by

  have he : ((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x))=(boundaryRePowerRow77_3Degree26Norm x).val+(boundaryRePowerRow77_4Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree26Norm x).property (boundaryRePowerRow77_4Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree26Norm,boundaryRePowerRow77_4Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x))))=(boundaryRePowerRow77_2Degree26Norm x).val+(boundaryFullPowerDegree26Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree26Norm x).property (boundaryFullPowerDegree26Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree26Norm,boundaryFullPowerDegree26Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x))))))=(boundaryFullPowerDegree26Block0Norm x).val+(boundaryFullPowerDegree26Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block0Norm x).property (boundaryFullPowerDegree26Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block0Norm,boundaryFullPowerDegree26Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x))=c} := by

  have he : ((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x))=(boundaryRePowerRow77_6Degree26Norm x).val+(boundaryRePowerRow77_7Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree26Norm x).property (boundaryRePowerRow77_7Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree26Norm,boundaryRePowerRow77_7Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x))))=(boundaryRePowerRow77_5Degree26Norm x).val+(boundaryFullPowerDegree26Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree26Norm x).property (boundaryFullPowerDegree26Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree26Norm,boundaryFullPowerDegree26Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))=c} := by

  have he : ((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))=(boundaryRePowerRow77_9Degree26Norm x).val+(boundaryRePowerRow77_10Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree26Norm x).property (boundaryRePowerRow77_10Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree26Norm,boundaryRePowerRow77_10Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))))=(boundaryRePowerRow77_8Degree26Norm x).val+(boundaryFullPowerDegree26Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree26Norm x).property (boundaryFullPowerDegree26Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree26Norm,boundaryFullPowerDegree26Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))))))=(boundaryFullPowerDegree26Block5Norm x).val+(boundaryFullPowerDegree26Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block5Norm x).property (boundaryFullPowerDegree26Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block5Norm,boundaryFullPowerDegree26Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x))))))))=(boundaryFullPowerDegree26Block3Norm x).val+(boundaryFullPowerDegree26Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block3Norm x).property (boundaryFullPowerDegree26Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block3Norm,boundaryFullPowerDegree26Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x))=c} := by

  have he : ((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x))=(boundaryRePowerRow77_12Degree26Norm x).val+(boundaryRePowerRow77_13Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree26Norm x).property (boundaryRePowerRow77_13Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree26Norm,boundaryRePowerRow77_13Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x))))=(boundaryRePowerRow77_11Degree26Norm x).val+(boundaryFullPowerDegree26Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree26Norm x).property (boundaryFullPowerDegree26Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree26Norm,boundaryFullPowerDegree26Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x))=c} := by

  have he : ((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x))=(boundaryRePowerRow77_15Degree26Norm x).val+(boundaryRePowerRow77_16Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree26Norm x).property (boundaryRePowerRow77_16Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree26Norm,boundaryRePowerRow77_16Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x))))=(boundaryRePowerRow77_14Degree26Norm x).val+(boundaryFullPowerDegree26Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree26Norm x).property (boundaryFullPowerDegree26Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree26Norm,boundaryFullPowerDegree26Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x))))))=(boundaryFullPowerDegree26Block11Norm x).val+(boundaryFullPowerDegree26Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block11Norm x).property (boundaryFullPowerDegree26Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block11Norm,boundaryFullPowerDegree26Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x))=c} := by

  have he : ((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x))=(boundaryRePowerRow77_18Degree26Norm x).val+(boundaryRePowerRow77_19Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree26Norm x).property (boundaryRePowerRow77_19Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree26Norm,boundaryRePowerRow77_19Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x))))=(boundaryRePowerRow77_17Degree26Norm x).val+(boundaryFullPowerDegree26Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree26Norm x).property (boundaryFullPowerDegree26Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree26Norm,boundaryFullPowerDegree26Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))=c} := by

  have he : ((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))=(boundaryRePowerRow77_21Degree26Norm x).val+(boundaryRePowerRow77_22Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree26Norm x).property (boundaryRePowerRow77_22Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree26Norm,boundaryRePowerRow77_22Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))=(boundaryRePowerRow77_20Degree26Norm x).val+(boundaryFullPowerDegree26Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree26Norm x).property (boundaryFullPowerDegree26Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree26Norm,boundaryFullPowerDegree26Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))))=(boundaryFullPowerDegree26Block16Norm x).val+(boundaryFullPowerDegree26Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block16Norm x).property (boundaryFullPowerDegree26Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block16Norm,boundaryFullPowerDegree26Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))))))=(boundaryFullPowerDegree26Block14Norm x).val+(boundaryFullPowerDegree26Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block14Norm x).property (boundaryFullPowerDegree26Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block14Norm,boundaryFullPowerDegree26Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x)))))))))+(((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x)))))))))+(((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x))))))))))=(boundaryFullPowerDegree26Block9Norm x).val+(boundaryFullPowerDegree26Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block9Norm x).property (boundaryFullPowerDegree26Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block9Norm,boundaryFullPowerDegree26Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x))=c} := by

  have he : ((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x))=(boundaryImPowerRow77_0Degree26Norm x).val+(boundaryImPowerRow77_1Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree26Norm x).property (boundaryImPowerRow77_1Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree26Norm,boundaryImPowerRow77_1Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x))=c} := by

  have he : ((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x))=(boundaryImPowerRow77_3Degree26Norm x).val+(boundaryImPowerRow77_4Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree26Norm x).property (boundaryImPowerRow77_4Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree26Norm,boundaryImPowerRow77_4Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x))))=(boundaryImPowerRow77_2Degree26Norm x).val+(boundaryFullPowerDegree26Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree26Norm x).property (boundaryFullPowerDegree26Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree26Norm,boundaryFullPowerDegree26Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x))))))=(boundaryFullPowerDegree26Block22Norm x).val+(boundaryFullPowerDegree26Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block22Norm x).property (boundaryFullPowerDegree26Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block22Norm,boundaryFullPowerDegree26Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x))=c} := by

  have he : ((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x))=(boundaryImPowerRow77_6Degree26Norm x).val+(boundaryImPowerRow77_7Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree26Norm x).property (boundaryImPowerRow77_7Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree26Norm,boundaryImPowerRow77_7Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x))))=(boundaryImPowerRow77_5Degree26Norm x).val+(boundaryFullPowerDegree26Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree26Norm x).property (boundaryFullPowerDegree26Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree26Norm,boundaryFullPowerDegree26Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))=c} := by

  have he : ((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))=(boundaryImPowerRow77_9Degree26Norm x).val+(boundaryImPowerRow77_10Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree26Norm x).property (boundaryImPowerRow77_10Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree26Norm,boundaryImPowerRow77_10Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))))=(boundaryImPowerRow77_8Degree26Norm x).val+(boundaryFullPowerDegree26Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree26Norm x).property (boundaryFullPowerDegree26Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree26Norm,boundaryFullPowerDegree26Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))))))=(boundaryFullPowerDegree26Block27Norm x).val+(boundaryFullPowerDegree26Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block27Norm x).property (boundaryFullPowerDegree26Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block27Norm,boundaryFullPowerDegree26Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x))))))))=(boundaryFullPowerDegree26Block25Norm x).val+(boundaryFullPowerDegree26Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block25Norm x).property (boundaryFullPowerDegree26Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block25Norm,boundaryFullPowerDegree26Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x))=c} := by

  have he : ((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x))=(boundaryImPowerRow77_12Degree26Norm x).val+(boundaryImPowerRow77_13Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree26Norm x).property (boundaryImPowerRow77_13Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree26Norm,boundaryImPowerRow77_13Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x))))=(boundaryImPowerRow77_11Degree26Norm x).val+(boundaryFullPowerDegree26Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree26Norm x).property (boundaryFullPowerDegree26Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree26Norm,boundaryFullPowerDegree26Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x))=c} := by

  have he : ((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x))=(boundaryImPowerRow77_15Degree26Norm x).val+(boundaryImPowerRow77_16Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree26Norm x).property (boundaryImPowerRow77_16Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree26Norm,boundaryImPowerRow77_16Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x))))=(boundaryImPowerRow77_14Degree26Norm x).val+(boundaryFullPowerDegree26Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree26Norm x).property (boundaryFullPowerDegree26Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree26Norm,boundaryFullPowerDegree26Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x))))))=(boundaryFullPowerDegree26Block33Norm x).val+(boundaryFullPowerDegree26Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block33Norm x).property (boundaryFullPowerDegree26Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block33Norm,boundaryFullPowerDegree26Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x))=c} := by

  have he : ((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x))=(boundaryImPowerRow77_18Degree26Norm x).val+(boundaryImPowerRow77_19Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree26Norm x).property (boundaryImPowerRow77_19Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree26Norm,boundaryImPowerRow77_19Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x))))=(boundaryImPowerRow77_17Degree26Norm x).val+(boundaryFullPowerDegree26Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree26Norm x).property (boundaryFullPowerDegree26Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree26Norm,boundaryFullPowerDegree26Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))=c} := by

  have he : ((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))=(boundaryImPowerRow77_21Degree26Norm x).val+(boundaryLowPowerRow77Degree26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree26Norm x).property (boundaryLowPowerRow77Degree26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree26Norm,boundaryLowPowerRow77Degree26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))=(boundaryImPowerRow77_20Degree26Norm x).val+(boundaryFullPowerDegree26Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree26Norm x).property (boundaryFullPowerDegree26Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree26Norm,boundaryFullPowerDegree26Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))=(boundaryFullPowerDegree26Block38Norm x).val+(boundaryFullPowerDegree26Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block38Norm x).property (boundaryFullPowerDegree26Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block38Norm,boundaryFullPowerDegree26Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))))=(boundaryFullPowerDegree26Block36Norm x).val+(boundaryFullPowerDegree26Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block36Norm x).property (boundaryFullPowerDegree26Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block36Norm,boundaryFullPowerDegree26Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x)))))))))+(((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x)))))))))+(((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))))))=(boundaryFullPowerDegree26Block31Norm x).val+(boundaryFullPowerDegree26Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block31Norm x).property (boundaryFullPowerDegree26Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block31Norm,boundaryFullPowerDegree26Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree26Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x)))))))))+(((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x)))))))))))+(((((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x)))))))))+(((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x)))))))))+(((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x)))))))))))+(((((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x)))))))))+(((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x))))))))))))=(boundaryFullPowerDegree26Block21Norm x).val+(boundaryFullPowerDegree26Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree26Block21Norm x).property (boundaryFullPowerDegree26Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block21Norm,boundaryFullPowerDegree26Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree26Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 26 x=c} := by

  have he0 : boundaryFullPowerRow77 26 x=((((((((((boundaryRePowerRow77_0 26 x)+(boundaryRePowerRow77_1 26 x)))+(((boundaryRePowerRow77_2 26 x)+(((boundaryRePowerRow77_3 26 x)+(boundaryRePowerRow77_4 26 x)))))))+(((((boundaryRePowerRow77_5 26 x)+(((boundaryRePowerRow77_6 26 x)+(boundaryRePowerRow77_7 26 x)))))+(((boundaryRePowerRow77_8 26 x)+(((boundaryRePowerRow77_9 26 x)+(boundaryRePowerRow77_10 26 x)))))))))+(((((((boundaryRePowerRow77_11 26 x)+(((boundaryRePowerRow77_12 26 x)+(boundaryRePowerRow77_13 26 x)))))+(((boundaryRePowerRow77_14 26 x)+(((boundaryRePowerRow77_15 26 x)+(boundaryRePowerRow77_16 26 x)))))))+(((((boundaryRePowerRow77_17 26 x)+(((boundaryRePowerRow77_18 26 x)+(boundaryRePowerRow77_19 26 x)))))+(((boundaryRePowerRow77_20 26 x)+(((boundaryRePowerRow77_21 26 x)+(boundaryRePowerRow77_22 26 x)))))))))))+(((((((((boundaryImPowerRow77_0 26 x)+(boundaryImPowerRow77_1 26 x)))+(((boundaryImPowerRow77_2 26 x)+(((boundaryImPowerRow77_3 26 x)+(boundaryImPowerRow77_4 26 x)))))))+(((((boundaryImPowerRow77_5 26 x)+(((boundaryImPowerRow77_6 26 x)+(boundaryImPowerRow77_7 26 x)))))+(((boundaryImPowerRow77_8 26 x)+(((boundaryImPowerRow77_9 26 x)+(boundaryImPowerRow77_10 26 x)))))))))+(((((((boundaryImPowerRow77_11 26 x)+(((boundaryImPowerRow77_12 26 x)+(boundaryImPowerRow77_13 26 x)))))+(((boundaryImPowerRow77_14 26 x)+(((boundaryImPowerRow77_15 26 x)+(boundaryImPowerRow77_16 26 x)))))))+(((((boundaryImPowerRow77_17 26 x)+(((boundaryImPowerRow77_18 26 x)+(boundaryImPowerRow77_19 26 x)))))+(((boundaryImPowerRow77_20 26 x)+(((boundaryImPowerRow77_21 26 x)+(boundaryLowPowerRow77 26 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree26Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree26Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
