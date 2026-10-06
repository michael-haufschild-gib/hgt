import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree36Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree36Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x))=c} := by

  have he : ((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x))=(boundaryRePowerRow77_0Degree36Norm x).val+(boundaryRePowerRow77_1Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree36Norm x).property (boundaryRePowerRow77_1Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree36Norm,boundaryRePowerRow77_1Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x))=c} := by

  have he : ((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x))=(boundaryRePowerRow77_3Degree36Norm x).val+(boundaryRePowerRow77_4Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree36Norm x).property (boundaryRePowerRow77_4Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree36Norm,boundaryRePowerRow77_4Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x))))=(boundaryRePowerRow77_2Degree36Norm x).val+(boundaryFullPowerDegree36Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree36Norm x).property (boundaryFullPowerDegree36Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree36Norm,boundaryFullPowerDegree36Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x))))))=(boundaryFullPowerDegree36Block0Norm x).val+(boundaryFullPowerDegree36Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block0Norm x).property (boundaryFullPowerDegree36Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block0Norm,boundaryFullPowerDegree36Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x))=c} := by

  have he : ((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x))=(boundaryRePowerRow77_6Degree36Norm x).val+(boundaryRePowerRow77_7Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree36Norm x).property (boundaryRePowerRow77_7Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree36Norm,boundaryRePowerRow77_7Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x))))=(boundaryRePowerRow77_5Degree36Norm x).val+(boundaryFullPowerDegree36Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree36Norm x).property (boundaryFullPowerDegree36Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree36Norm,boundaryFullPowerDegree36Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))=c} := by

  have he : ((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))=(boundaryRePowerRow77_9Degree36Norm x).val+(boundaryRePowerRow77_10Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree36Norm x).property (boundaryRePowerRow77_10Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree36Norm,boundaryRePowerRow77_10Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))))=(boundaryRePowerRow77_8Degree36Norm x).val+(boundaryFullPowerDegree36Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree36Norm x).property (boundaryFullPowerDegree36Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree36Norm,boundaryFullPowerDegree36Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))))))=(boundaryFullPowerDegree36Block5Norm x).val+(boundaryFullPowerDegree36Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block5Norm x).property (boundaryFullPowerDegree36Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block5Norm,boundaryFullPowerDegree36Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x))))))))=(boundaryFullPowerDegree36Block3Norm x).val+(boundaryFullPowerDegree36Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block3Norm x).property (boundaryFullPowerDegree36Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block3Norm,boundaryFullPowerDegree36Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x))=c} := by

  have he : ((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x))=(boundaryRePowerRow77_12Degree36Norm x).val+(boundaryRePowerRow77_13Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree36Norm x).property (boundaryRePowerRow77_13Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree36Norm,boundaryRePowerRow77_13Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x))))=(boundaryRePowerRow77_11Degree36Norm x).val+(boundaryFullPowerDegree36Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree36Norm x).property (boundaryFullPowerDegree36Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree36Norm,boundaryFullPowerDegree36Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x))=c} := by

  have he : ((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x))=(boundaryRePowerRow77_15Degree36Norm x).val+(boundaryRePowerRow77_16Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree36Norm x).property (boundaryRePowerRow77_16Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree36Norm,boundaryRePowerRow77_16Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x))))=(boundaryRePowerRow77_14Degree36Norm x).val+(boundaryFullPowerDegree36Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree36Norm x).property (boundaryFullPowerDegree36Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree36Norm,boundaryFullPowerDegree36Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x))))))=(boundaryFullPowerDegree36Block11Norm x).val+(boundaryFullPowerDegree36Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block11Norm x).property (boundaryFullPowerDegree36Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block11Norm,boundaryFullPowerDegree36Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x))=c} := by

  have he : ((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x))=(boundaryRePowerRow77_18Degree36Norm x).val+(boundaryRePowerRow77_19Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree36Norm x).property (boundaryRePowerRow77_19Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree36Norm,boundaryRePowerRow77_19Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x))))=(boundaryRePowerRow77_17Degree36Norm x).val+(boundaryFullPowerDegree36Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree36Norm x).property (boundaryFullPowerDegree36Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree36Norm,boundaryFullPowerDegree36Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))=c} := by

  have he : ((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))=(boundaryRePowerRow77_21Degree36Norm x).val+(boundaryRePowerRow77_22Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree36Norm x).property (boundaryRePowerRow77_22Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree36Norm,boundaryRePowerRow77_22Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))=(boundaryRePowerRow77_20Degree36Norm x).val+(boundaryFullPowerDegree36Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree36Norm x).property (boundaryFullPowerDegree36Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree36Norm,boundaryFullPowerDegree36Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))))=(boundaryFullPowerDegree36Block16Norm x).val+(boundaryFullPowerDegree36Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block16Norm x).property (boundaryFullPowerDegree36Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block16Norm,boundaryFullPowerDegree36Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))))))=(boundaryFullPowerDegree36Block14Norm x).val+(boundaryFullPowerDegree36Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block14Norm x).property (boundaryFullPowerDegree36Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block14Norm,boundaryFullPowerDegree36Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x)))))))))+(((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x)))))))))+(((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x))))))))))=(boundaryFullPowerDegree36Block9Norm x).val+(boundaryFullPowerDegree36Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block9Norm x).property (boundaryFullPowerDegree36Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block9Norm,boundaryFullPowerDegree36Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x))=c} := by

  have he : ((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x))=(boundaryImPowerRow77_0Degree36Norm x).val+(boundaryImPowerRow77_1Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree36Norm x).property (boundaryImPowerRow77_1Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree36Norm,boundaryImPowerRow77_1Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x))=c} := by

  have he : ((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x))=(boundaryImPowerRow77_3Degree36Norm x).val+(boundaryImPowerRow77_4Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree36Norm x).property (boundaryImPowerRow77_4Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree36Norm,boundaryImPowerRow77_4Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x))))=(boundaryImPowerRow77_2Degree36Norm x).val+(boundaryFullPowerDegree36Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree36Norm x).property (boundaryFullPowerDegree36Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree36Norm,boundaryFullPowerDegree36Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x))))))=(boundaryFullPowerDegree36Block22Norm x).val+(boundaryFullPowerDegree36Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block22Norm x).property (boundaryFullPowerDegree36Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block22Norm,boundaryFullPowerDegree36Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x))=c} := by

  have he : ((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x))=(boundaryImPowerRow77_6Degree36Norm x).val+(boundaryImPowerRow77_7Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree36Norm x).property (boundaryImPowerRow77_7Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree36Norm,boundaryImPowerRow77_7Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x))))=(boundaryImPowerRow77_5Degree36Norm x).val+(boundaryFullPowerDegree36Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree36Norm x).property (boundaryFullPowerDegree36Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree36Norm,boundaryFullPowerDegree36Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))=c} := by

  have he : ((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))=(boundaryImPowerRow77_9Degree36Norm x).val+(boundaryImPowerRow77_10Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree36Norm x).property (boundaryImPowerRow77_10Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree36Norm,boundaryImPowerRow77_10Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))))=(boundaryImPowerRow77_8Degree36Norm x).val+(boundaryFullPowerDegree36Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree36Norm x).property (boundaryFullPowerDegree36Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree36Norm,boundaryFullPowerDegree36Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))))))=(boundaryFullPowerDegree36Block27Norm x).val+(boundaryFullPowerDegree36Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block27Norm x).property (boundaryFullPowerDegree36Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block27Norm,boundaryFullPowerDegree36Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x))))))))=(boundaryFullPowerDegree36Block25Norm x).val+(boundaryFullPowerDegree36Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block25Norm x).property (boundaryFullPowerDegree36Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block25Norm,boundaryFullPowerDegree36Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x))=c} := by

  have he : ((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x))=(boundaryImPowerRow77_12Degree36Norm x).val+(boundaryImPowerRow77_13Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree36Norm x).property (boundaryImPowerRow77_13Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree36Norm,boundaryImPowerRow77_13Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x))))=(boundaryImPowerRow77_11Degree36Norm x).val+(boundaryFullPowerDegree36Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree36Norm x).property (boundaryFullPowerDegree36Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree36Norm,boundaryFullPowerDegree36Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x))=c} := by

  have he : ((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x))=(boundaryImPowerRow77_15Degree36Norm x).val+(boundaryImPowerRow77_16Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree36Norm x).property (boundaryImPowerRow77_16Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree36Norm,boundaryImPowerRow77_16Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x))))=(boundaryImPowerRow77_14Degree36Norm x).val+(boundaryFullPowerDegree36Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree36Norm x).property (boundaryFullPowerDegree36Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree36Norm,boundaryFullPowerDegree36Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x))))))=(boundaryFullPowerDegree36Block33Norm x).val+(boundaryFullPowerDegree36Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block33Norm x).property (boundaryFullPowerDegree36Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block33Norm,boundaryFullPowerDegree36Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x))=c} := by

  have he : ((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x))=(boundaryImPowerRow77_18Degree36Norm x).val+(boundaryImPowerRow77_19Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree36Norm x).property (boundaryImPowerRow77_19Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree36Norm,boundaryImPowerRow77_19Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x))))=(boundaryImPowerRow77_17Degree36Norm x).val+(boundaryFullPowerDegree36Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree36Norm x).property (boundaryFullPowerDegree36Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree36Norm,boundaryFullPowerDegree36Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))=c} := by

  have he : ((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))=(boundaryImPowerRow77_21Degree36Norm x).val+(boundaryLowPowerRow77Degree36Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree36Norm x).property (boundaryLowPowerRow77Degree36Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree36Norm,boundaryLowPowerRow77Degree36Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))=(boundaryImPowerRow77_20Degree36Norm x).val+(boundaryFullPowerDegree36Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree36Norm x).property (boundaryFullPowerDegree36Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree36Norm,boundaryFullPowerDegree36Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))=(boundaryFullPowerDegree36Block38Norm x).val+(boundaryFullPowerDegree36Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block38Norm x).property (boundaryFullPowerDegree36Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block38Norm,boundaryFullPowerDegree36Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))))=(boundaryFullPowerDegree36Block36Norm x).val+(boundaryFullPowerDegree36Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block36Norm x).property (boundaryFullPowerDegree36Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block36Norm,boundaryFullPowerDegree36Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x)))))))))+(((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x)))))))))+(((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))))))=(boundaryFullPowerDegree36Block31Norm x).val+(boundaryFullPowerDegree36Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block31Norm x).property (boundaryFullPowerDegree36Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block31Norm,boundaryFullPowerDegree36Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree36Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x)))))))))+(((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x)))))))))))+(((((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x)))))))))+(((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x)))))))))+(((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x)))))))))))+(((((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x)))))))))+(((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x))))))))))))=(boundaryFullPowerDegree36Block21Norm x).val+(boundaryFullPowerDegree36Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree36Block21Norm x).property (boundaryFullPowerDegree36Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block21Norm,boundaryFullPowerDegree36Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree36Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 36 x=c} := by

  have he0 : boundaryFullPowerRow77 36 x=((((((((((boundaryRePowerRow77_0 36 x)+(boundaryRePowerRow77_1 36 x)))+(((boundaryRePowerRow77_2 36 x)+(((boundaryRePowerRow77_3 36 x)+(boundaryRePowerRow77_4 36 x)))))))+(((((boundaryRePowerRow77_5 36 x)+(((boundaryRePowerRow77_6 36 x)+(boundaryRePowerRow77_7 36 x)))))+(((boundaryRePowerRow77_8 36 x)+(((boundaryRePowerRow77_9 36 x)+(boundaryRePowerRow77_10 36 x)))))))))+(((((((boundaryRePowerRow77_11 36 x)+(((boundaryRePowerRow77_12 36 x)+(boundaryRePowerRow77_13 36 x)))))+(((boundaryRePowerRow77_14 36 x)+(((boundaryRePowerRow77_15 36 x)+(boundaryRePowerRow77_16 36 x)))))))+(((((boundaryRePowerRow77_17 36 x)+(((boundaryRePowerRow77_18 36 x)+(boundaryRePowerRow77_19 36 x)))))+(((boundaryRePowerRow77_20 36 x)+(((boundaryRePowerRow77_21 36 x)+(boundaryRePowerRow77_22 36 x)))))))))))+(((((((((boundaryImPowerRow77_0 36 x)+(boundaryImPowerRow77_1 36 x)))+(((boundaryImPowerRow77_2 36 x)+(((boundaryImPowerRow77_3 36 x)+(boundaryImPowerRow77_4 36 x)))))))+(((((boundaryImPowerRow77_5 36 x)+(((boundaryImPowerRow77_6 36 x)+(boundaryImPowerRow77_7 36 x)))))+(((boundaryImPowerRow77_8 36 x)+(((boundaryImPowerRow77_9 36 x)+(boundaryImPowerRow77_10 36 x)))))))))+(((((((boundaryImPowerRow77_11 36 x)+(((boundaryImPowerRow77_12 36 x)+(boundaryImPowerRow77_13 36 x)))))+(((boundaryImPowerRow77_14 36 x)+(((boundaryImPowerRow77_15 36 x)+(boundaryImPowerRow77_16 36 x)))))))+(((((boundaryImPowerRow77_17 36 x)+(((boundaryImPowerRow77_18 36 x)+(boundaryImPowerRow77_19 36 x)))))+(((boundaryImPowerRow77_20 36 x)+(((boundaryImPowerRow77_21 36 x)+(boundaryLowPowerRow77 36 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree36Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree36Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
