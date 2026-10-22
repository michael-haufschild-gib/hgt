import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree90Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree90Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x))=c} := by

  have he : ((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x))=(boundaryRePowerRow77_0Degree90Norm x).val+(boundaryRePowerRow77_1Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree90Norm x).property (boundaryRePowerRow77_1Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree90Norm,boundaryRePowerRow77_1Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x))=c} := by

  have he : ((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x))=(boundaryRePowerRow77_3Degree90Norm x).val+(boundaryRePowerRow77_4Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree90Norm x).property (boundaryRePowerRow77_4Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree90Norm,boundaryRePowerRow77_4Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x))))=(boundaryRePowerRow77_2Degree90Norm x).val+(boundaryFullPowerDegree90Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree90Norm x).property (boundaryFullPowerDegree90Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree90Norm,boundaryFullPowerDegree90Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x))))))=(boundaryFullPowerDegree90Block0Norm x).val+(boundaryFullPowerDegree90Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block0Norm x).property (boundaryFullPowerDegree90Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block0Norm,boundaryFullPowerDegree90Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x))=c} := by

  have he : ((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x))=(boundaryRePowerRow77_6Degree90Norm x).val+(boundaryRePowerRow77_7Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree90Norm x).property (boundaryRePowerRow77_7Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree90Norm,boundaryRePowerRow77_7Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x))))=(boundaryRePowerRow77_5Degree90Norm x).val+(boundaryFullPowerDegree90Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree90Norm x).property (boundaryFullPowerDegree90Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree90Norm,boundaryFullPowerDegree90Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))=c} := by

  have he : ((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))=(boundaryRePowerRow77_9Degree90Norm x).val+(boundaryRePowerRow77_10Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree90Norm x).property (boundaryRePowerRow77_10Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree90Norm,boundaryRePowerRow77_10Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))))=(boundaryRePowerRow77_8Degree90Norm x).val+(boundaryFullPowerDegree90Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree90Norm x).property (boundaryFullPowerDegree90Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree90Norm,boundaryFullPowerDegree90Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))))))=(boundaryFullPowerDegree90Block5Norm x).val+(boundaryFullPowerDegree90Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block5Norm x).property (boundaryFullPowerDegree90Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block5Norm,boundaryFullPowerDegree90Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x))))))))=(boundaryFullPowerDegree90Block3Norm x).val+(boundaryFullPowerDegree90Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block3Norm x).property (boundaryFullPowerDegree90Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block3Norm,boundaryFullPowerDegree90Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x))=c} := by

  have he : ((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x))=(boundaryRePowerRow77_12Degree90Norm x).val+(boundaryRePowerRow77_13Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree90Norm x).property (boundaryRePowerRow77_13Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree90Norm,boundaryRePowerRow77_13Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x))))=(boundaryRePowerRow77_11Degree90Norm x).val+(boundaryFullPowerDegree90Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree90Norm x).property (boundaryFullPowerDegree90Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree90Norm,boundaryFullPowerDegree90Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x))=c} := by

  have he : ((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x))=(boundaryRePowerRow77_15Degree90Norm x).val+(boundaryRePowerRow77_16Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree90Norm x).property (boundaryRePowerRow77_16Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree90Norm,boundaryRePowerRow77_16Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x))))=(boundaryRePowerRow77_14Degree90Norm x).val+(boundaryFullPowerDegree90Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree90Norm x).property (boundaryFullPowerDegree90Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree90Norm,boundaryFullPowerDegree90Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x))))))=(boundaryFullPowerDegree90Block11Norm x).val+(boundaryFullPowerDegree90Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block11Norm x).property (boundaryFullPowerDegree90Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block11Norm,boundaryFullPowerDegree90Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x))=c} := by

  have he : ((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x))=(boundaryRePowerRow77_18Degree90Norm x).val+(boundaryRePowerRow77_19Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree90Norm x).property (boundaryRePowerRow77_19Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree90Norm,boundaryRePowerRow77_19Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x))))=(boundaryRePowerRow77_17Degree90Norm x).val+(boundaryFullPowerDegree90Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree90Norm x).property (boundaryFullPowerDegree90Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree90Norm,boundaryFullPowerDegree90Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))=c} := by

  have he : ((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))=(boundaryRePowerRow77_21Degree90Norm x).val+(boundaryRePowerRow77_22Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree90Norm x).property (boundaryRePowerRow77_22Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree90Norm,boundaryRePowerRow77_22Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))=(boundaryRePowerRow77_20Degree90Norm x).val+(boundaryFullPowerDegree90Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree90Norm x).property (boundaryFullPowerDegree90Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree90Norm,boundaryFullPowerDegree90Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))))=(boundaryFullPowerDegree90Block16Norm x).val+(boundaryFullPowerDegree90Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block16Norm x).property (boundaryFullPowerDegree90Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block16Norm,boundaryFullPowerDegree90Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))))))=(boundaryFullPowerDegree90Block14Norm x).val+(boundaryFullPowerDegree90Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block14Norm x).property (boundaryFullPowerDegree90Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block14Norm,boundaryFullPowerDegree90Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x)))))))))+(((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x)))))))))+(((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x))))))))))=(boundaryFullPowerDegree90Block9Norm x).val+(boundaryFullPowerDegree90Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block9Norm x).property (boundaryFullPowerDegree90Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block9Norm,boundaryFullPowerDegree90Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x))=c} := by

  have he : ((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x))=(boundaryImPowerRow77_0Degree90Norm x).val+(boundaryImPowerRow77_1Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree90Norm x).property (boundaryImPowerRow77_1Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree90Norm,boundaryImPowerRow77_1Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x))=c} := by

  have he : ((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x))=(boundaryImPowerRow77_3Degree90Norm x).val+(boundaryImPowerRow77_4Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree90Norm x).property (boundaryImPowerRow77_4Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree90Norm,boundaryImPowerRow77_4Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x))))=(boundaryImPowerRow77_2Degree90Norm x).val+(boundaryFullPowerDegree90Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree90Norm x).property (boundaryFullPowerDegree90Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree90Norm,boundaryFullPowerDegree90Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x))))))=(boundaryFullPowerDegree90Block22Norm x).val+(boundaryFullPowerDegree90Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block22Norm x).property (boundaryFullPowerDegree90Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block22Norm,boundaryFullPowerDegree90Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x))=c} := by

  have he : ((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x))=(boundaryImPowerRow77_6Degree90Norm x).val+(boundaryImPowerRow77_7Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree90Norm x).property (boundaryImPowerRow77_7Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree90Norm,boundaryImPowerRow77_7Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x))))=(boundaryImPowerRow77_5Degree90Norm x).val+(boundaryFullPowerDegree90Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree90Norm x).property (boundaryFullPowerDegree90Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree90Norm,boundaryFullPowerDegree90Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))=c} := by

  have he : ((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))=(boundaryImPowerRow77_9Degree90Norm x).val+(boundaryImPowerRow77_10Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree90Norm x).property (boundaryImPowerRow77_10Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree90Norm,boundaryImPowerRow77_10Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))))=(boundaryImPowerRow77_8Degree90Norm x).val+(boundaryFullPowerDegree90Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree90Norm x).property (boundaryFullPowerDegree90Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree90Norm,boundaryFullPowerDegree90Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))))))=(boundaryFullPowerDegree90Block27Norm x).val+(boundaryFullPowerDegree90Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block27Norm x).property (boundaryFullPowerDegree90Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block27Norm,boundaryFullPowerDegree90Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x))))))))=(boundaryFullPowerDegree90Block25Norm x).val+(boundaryFullPowerDegree90Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block25Norm x).property (boundaryFullPowerDegree90Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block25Norm,boundaryFullPowerDegree90Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x))=c} := by

  have he : ((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x))=(boundaryImPowerRow77_12Degree90Norm x).val+(boundaryImPowerRow77_13Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree90Norm x).property (boundaryImPowerRow77_13Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree90Norm,boundaryImPowerRow77_13Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x))))=(boundaryImPowerRow77_11Degree90Norm x).val+(boundaryFullPowerDegree90Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree90Norm x).property (boundaryFullPowerDegree90Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree90Norm,boundaryFullPowerDegree90Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x))=c} := by

  have he : ((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x))=(boundaryImPowerRow77_15Degree90Norm x).val+(boundaryImPowerRow77_16Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree90Norm x).property (boundaryImPowerRow77_16Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree90Norm,boundaryImPowerRow77_16Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x))))=(boundaryImPowerRow77_14Degree90Norm x).val+(boundaryFullPowerDegree90Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree90Norm x).property (boundaryFullPowerDegree90Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree90Norm,boundaryFullPowerDegree90Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x))))))=(boundaryFullPowerDegree90Block33Norm x).val+(boundaryFullPowerDegree90Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block33Norm x).property (boundaryFullPowerDegree90Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block33Norm,boundaryFullPowerDegree90Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x))=c} := by

  have he : ((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x))=(boundaryImPowerRow77_18Degree90Norm x).val+(boundaryImPowerRow77_19Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree90Norm x).property (boundaryImPowerRow77_19Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree90Norm,boundaryImPowerRow77_19Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x))))=(boundaryImPowerRow77_17Degree90Norm x).val+(boundaryFullPowerDegree90Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree90Norm x).property (boundaryFullPowerDegree90Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree90Norm,boundaryFullPowerDegree90Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))=c} := by

  have he : ((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))=(boundaryImPowerRow77_21Degree90Norm x).val+(boundaryLowPowerRow77Degree90Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree90Norm x).property (boundaryLowPowerRow77Degree90Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree90Norm,boundaryLowPowerRow77Degree90Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))=(boundaryImPowerRow77_20Degree90Norm x).val+(boundaryFullPowerDegree90Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree90Norm x).property (boundaryFullPowerDegree90Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree90Norm,boundaryFullPowerDegree90Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))=(boundaryFullPowerDegree90Block38Norm x).val+(boundaryFullPowerDegree90Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block38Norm x).property (boundaryFullPowerDegree90Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block38Norm,boundaryFullPowerDegree90Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))))=(boundaryFullPowerDegree90Block36Norm x).val+(boundaryFullPowerDegree90Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block36Norm x).property (boundaryFullPowerDegree90Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block36Norm,boundaryFullPowerDegree90Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x)))))))))+(((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x)))))))))+(((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))))))=(boundaryFullPowerDegree90Block31Norm x).val+(boundaryFullPowerDegree90Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block31Norm x).property (boundaryFullPowerDegree90Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block31Norm,boundaryFullPowerDegree90Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree90Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x)))))))))+(((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x)))))))))))+(((((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x)))))))))+(((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x)))))))))+(((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x)))))))))))+(((((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x)))))))))+(((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x))))))))))))=(boundaryFullPowerDegree90Block21Norm x).val+(boundaryFullPowerDegree90Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree90Block21Norm x).property (boundaryFullPowerDegree90Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block21Norm,boundaryFullPowerDegree90Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree90Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 90 x=c} := by

  have he0 : boundaryFullPowerRow77 90 x=((((((((((boundaryRePowerRow77_0 90 x)+(boundaryRePowerRow77_1 90 x)))+(((boundaryRePowerRow77_2 90 x)+(((boundaryRePowerRow77_3 90 x)+(boundaryRePowerRow77_4 90 x)))))))+(((((boundaryRePowerRow77_5 90 x)+(((boundaryRePowerRow77_6 90 x)+(boundaryRePowerRow77_7 90 x)))))+(((boundaryRePowerRow77_8 90 x)+(((boundaryRePowerRow77_9 90 x)+(boundaryRePowerRow77_10 90 x)))))))))+(((((((boundaryRePowerRow77_11 90 x)+(((boundaryRePowerRow77_12 90 x)+(boundaryRePowerRow77_13 90 x)))))+(((boundaryRePowerRow77_14 90 x)+(((boundaryRePowerRow77_15 90 x)+(boundaryRePowerRow77_16 90 x)))))))+(((((boundaryRePowerRow77_17 90 x)+(((boundaryRePowerRow77_18 90 x)+(boundaryRePowerRow77_19 90 x)))))+(((boundaryRePowerRow77_20 90 x)+(((boundaryRePowerRow77_21 90 x)+(boundaryRePowerRow77_22 90 x)))))))))))+(((((((((boundaryImPowerRow77_0 90 x)+(boundaryImPowerRow77_1 90 x)))+(((boundaryImPowerRow77_2 90 x)+(((boundaryImPowerRow77_3 90 x)+(boundaryImPowerRow77_4 90 x)))))))+(((((boundaryImPowerRow77_5 90 x)+(((boundaryImPowerRow77_6 90 x)+(boundaryImPowerRow77_7 90 x)))))+(((boundaryImPowerRow77_8 90 x)+(((boundaryImPowerRow77_9 90 x)+(boundaryImPowerRow77_10 90 x)))))))))+(((((((boundaryImPowerRow77_11 90 x)+(((boundaryImPowerRow77_12 90 x)+(boundaryImPowerRow77_13 90 x)))))+(((boundaryImPowerRow77_14 90 x)+(((boundaryImPowerRow77_15 90 x)+(boundaryImPowerRow77_16 90 x)))))))+(((((boundaryImPowerRow77_17 90 x)+(((boundaryImPowerRow77_18 90 x)+(boundaryImPowerRow77_19 90 x)))))+(((boundaryImPowerRow77_20 90 x)+(((boundaryImPowerRow77_21 90 x)+(boundaryLowPowerRow77 90 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree90Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree90Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
