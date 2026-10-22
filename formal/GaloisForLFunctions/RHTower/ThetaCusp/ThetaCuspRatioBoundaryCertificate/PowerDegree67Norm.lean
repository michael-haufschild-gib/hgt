import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree67Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree67Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x))=c} := by

  have he : ((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x))=(boundaryRePowerRow77_0Degree67Norm x).val+(boundaryRePowerRow77_1Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree67Norm x).property (boundaryRePowerRow77_1Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree67Norm,boundaryRePowerRow77_1Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x))=c} := by

  have he : ((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x))=(boundaryRePowerRow77_3Degree67Norm x).val+(boundaryRePowerRow77_4Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree67Norm x).property (boundaryRePowerRow77_4Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree67Norm,boundaryRePowerRow77_4Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x))))=(boundaryRePowerRow77_2Degree67Norm x).val+(boundaryFullPowerDegree67Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree67Norm x).property (boundaryFullPowerDegree67Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree67Norm,boundaryFullPowerDegree67Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x))))))=(boundaryFullPowerDegree67Block0Norm x).val+(boundaryFullPowerDegree67Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block0Norm x).property (boundaryFullPowerDegree67Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block0Norm,boundaryFullPowerDegree67Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x))=c} := by

  have he : ((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x))=(boundaryRePowerRow77_6Degree67Norm x).val+(boundaryRePowerRow77_7Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree67Norm x).property (boundaryRePowerRow77_7Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree67Norm,boundaryRePowerRow77_7Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x))))=(boundaryRePowerRow77_5Degree67Norm x).val+(boundaryFullPowerDegree67Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree67Norm x).property (boundaryFullPowerDegree67Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree67Norm,boundaryFullPowerDegree67Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))=c} := by

  have he : ((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))=(boundaryRePowerRow77_9Degree67Norm x).val+(boundaryRePowerRow77_10Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree67Norm x).property (boundaryRePowerRow77_10Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree67Norm,boundaryRePowerRow77_10Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))))=(boundaryRePowerRow77_8Degree67Norm x).val+(boundaryFullPowerDegree67Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree67Norm x).property (boundaryFullPowerDegree67Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree67Norm,boundaryFullPowerDegree67Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))))))=(boundaryFullPowerDegree67Block5Norm x).val+(boundaryFullPowerDegree67Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block5Norm x).property (boundaryFullPowerDegree67Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block5Norm,boundaryFullPowerDegree67Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x))))))))=(boundaryFullPowerDegree67Block3Norm x).val+(boundaryFullPowerDegree67Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block3Norm x).property (boundaryFullPowerDegree67Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block3Norm,boundaryFullPowerDegree67Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x))=c} := by

  have he : ((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x))=(boundaryRePowerRow77_12Degree67Norm x).val+(boundaryRePowerRow77_13Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree67Norm x).property (boundaryRePowerRow77_13Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree67Norm,boundaryRePowerRow77_13Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x))))=(boundaryRePowerRow77_11Degree67Norm x).val+(boundaryFullPowerDegree67Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree67Norm x).property (boundaryFullPowerDegree67Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree67Norm,boundaryFullPowerDegree67Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x))=c} := by

  have he : ((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x))=(boundaryRePowerRow77_15Degree67Norm x).val+(boundaryRePowerRow77_16Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree67Norm x).property (boundaryRePowerRow77_16Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree67Norm,boundaryRePowerRow77_16Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x))))=(boundaryRePowerRow77_14Degree67Norm x).val+(boundaryFullPowerDegree67Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree67Norm x).property (boundaryFullPowerDegree67Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree67Norm,boundaryFullPowerDegree67Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x))))))=(boundaryFullPowerDegree67Block11Norm x).val+(boundaryFullPowerDegree67Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block11Norm x).property (boundaryFullPowerDegree67Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block11Norm,boundaryFullPowerDegree67Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x))=c} := by

  have he : ((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x))=(boundaryRePowerRow77_18Degree67Norm x).val+(boundaryRePowerRow77_19Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree67Norm x).property (boundaryRePowerRow77_19Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree67Norm,boundaryRePowerRow77_19Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x))))=(boundaryRePowerRow77_17Degree67Norm x).val+(boundaryFullPowerDegree67Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree67Norm x).property (boundaryFullPowerDegree67Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree67Norm,boundaryFullPowerDegree67Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))=c} := by

  have he : ((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))=(boundaryRePowerRow77_21Degree67Norm x).val+(boundaryRePowerRow77_22Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree67Norm x).property (boundaryRePowerRow77_22Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree67Norm,boundaryRePowerRow77_22Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))=(boundaryRePowerRow77_20Degree67Norm x).val+(boundaryFullPowerDegree67Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree67Norm x).property (boundaryFullPowerDegree67Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree67Norm,boundaryFullPowerDegree67Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))))=(boundaryFullPowerDegree67Block16Norm x).val+(boundaryFullPowerDegree67Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block16Norm x).property (boundaryFullPowerDegree67Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block16Norm,boundaryFullPowerDegree67Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))))))=(boundaryFullPowerDegree67Block14Norm x).val+(boundaryFullPowerDegree67Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block14Norm x).property (boundaryFullPowerDegree67Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block14Norm,boundaryFullPowerDegree67Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x)))))))))+(((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x)))))))))+(((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x))))))))))=(boundaryFullPowerDegree67Block9Norm x).val+(boundaryFullPowerDegree67Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block9Norm x).property (boundaryFullPowerDegree67Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block9Norm,boundaryFullPowerDegree67Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x))=c} := by

  have he : ((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x))=(boundaryImPowerRow77_0Degree67Norm x).val+(boundaryImPowerRow77_1Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree67Norm x).property (boundaryImPowerRow77_1Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree67Norm,boundaryImPowerRow77_1Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x))=c} := by

  have he : ((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x))=(boundaryImPowerRow77_3Degree67Norm x).val+(boundaryImPowerRow77_4Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree67Norm x).property (boundaryImPowerRow77_4Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree67Norm,boundaryImPowerRow77_4Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x))))=(boundaryImPowerRow77_2Degree67Norm x).val+(boundaryFullPowerDegree67Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree67Norm x).property (boundaryFullPowerDegree67Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree67Norm,boundaryFullPowerDegree67Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x))))))=(boundaryFullPowerDegree67Block22Norm x).val+(boundaryFullPowerDegree67Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block22Norm x).property (boundaryFullPowerDegree67Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block22Norm,boundaryFullPowerDegree67Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x))=c} := by

  have he : ((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x))=(boundaryImPowerRow77_6Degree67Norm x).val+(boundaryImPowerRow77_7Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree67Norm x).property (boundaryImPowerRow77_7Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree67Norm,boundaryImPowerRow77_7Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x))))=(boundaryImPowerRow77_5Degree67Norm x).val+(boundaryFullPowerDegree67Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree67Norm x).property (boundaryFullPowerDegree67Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree67Norm,boundaryFullPowerDegree67Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))=c} := by

  have he : ((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))=(boundaryImPowerRow77_9Degree67Norm x).val+(boundaryImPowerRow77_10Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree67Norm x).property (boundaryImPowerRow77_10Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree67Norm,boundaryImPowerRow77_10Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))))=(boundaryImPowerRow77_8Degree67Norm x).val+(boundaryFullPowerDegree67Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree67Norm x).property (boundaryFullPowerDegree67Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree67Norm,boundaryFullPowerDegree67Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))))))=(boundaryFullPowerDegree67Block27Norm x).val+(boundaryFullPowerDegree67Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block27Norm x).property (boundaryFullPowerDegree67Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block27Norm,boundaryFullPowerDegree67Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x))))))))=(boundaryFullPowerDegree67Block25Norm x).val+(boundaryFullPowerDegree67Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block25Norm x).property (boundaryFullPowerDegree67Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block25Norm,boundaryFullPowerDegree67Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x))=c} := by

  have he : ((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x))=(boundaryImPowerRow77_12Degree67Norm x).val+(boundaryImPowerRow77_13Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree67Norm x).property (boundaryImPowerRow77_13Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree67Norm,boundaryImPowerRow77_13Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x))))=(boundaryImPowerRow77_11Degree67Norm x).val+(boundaryFullPowerDegree67Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree67Norm x).property (boundaryFullPowerDegree67Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree67Norm,boundaryFullPowerDegree67Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x))=c} := by

  have he : ((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x))=(boundaryImPowerRow77_15Degree67Norm x).val+(boundaryImPowerRow77_16Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree67Norm x).property (boundaryImPowerRow77_16Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree67Norm,boundaryImPowerRow77_16Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x))))=(boundaryImPowerRow77_14Degree67Norm x).val+(boundaryFullPowerDegree67Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree67Norm x).property (boundaryFullPowerDegree67Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree67Norm,boundaryFullPowerDegree67Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x))))))=(boundaryFullPowerDegree67Block33Norm x).val+(boundaryFullPowerDegree67Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block33Norm x).property (boundaryFullPowerDegree67Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block33Norm,boundaryFullPowerDegree67Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x))=c} := by

  have he : ((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x))=(boundaryImPowerRow77_18Degree67Norm x).val+(boundaryImPowerRow77_19Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree67Norm x).property (boundaryImPowerRow77_19Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree67Norm,boundaryImPowerRow77_19Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x))))=(boundaryImPowerRow77_17Degree67Norm x).val+(boundaryFullPowerDegree67Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree67Norm x).property (boundaryFullPowerDegree67Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree67Norm,boundaryFullPowerDegree67Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))=c} := by

  have he : ((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))=(boundaryImPowerRow77_21Degree67Norm x).val+(boundaryLowPowerRow77Degree67Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree67Norm x).property (boundaryLowPowerRow77Degree67Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree67Norm,boundaryLowPowerRow77Degree67Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))=(boundaryImPowerRow77_20Degree67Norm x).val+(boundaryFullPowerDegree67Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree67Norm x).property (boundaryFullPowerDegree67Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree67Norm,boundaryFullPowerDegree67Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))=(boundaryFullPowerDegree67Block38Norm x).val+(boundaryFullPowerDegree67Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block38Norm x).property (boundaryFullPowerDegree67Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block38Norm,boundaryFullPowerDegree67Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))))=(boundaryFullPowerDegree67Block36Norm x).val+(boundaryFullPowerDegree67Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block36Norm x).property (boundaryFullPowerDegree67Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block36Norm,boundaryFullPowerDegree67Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x)))))))))+(((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x)))))))))+(((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))))))=(boundaryFullPowerDegree67Block31Norm x).val+(boundaryFullPowerDegree67Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block31Norm x).property (boundaryFullPowerDegree67Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block31Norm,boundaryFullPowerDegree67Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree67Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x)))))))))+(((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x)))))))))))+(((((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x)))))))))+(((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x)))))))))+(((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x)))))))))))+(((((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x)))))))))+(((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x))))))))))))=(boundaryFullPowerDegree67Block21Norm x).val+(boundaryFullPowerDegree67Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree67Block21Norm x).property (boundaryFullPowerDegree67Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block21Norm,boundaryFullPowerDegree67Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree67Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 67 x=c} := by

  have he0 : boundaryFullPowerRow77 67 x=((((((((((boundaryRePowerRow77_0 67 x)+(boundaryRePowerRow77_1 67 x)))+(((boundaryRePowerRow77_2 67 x)+(((boundaryRePowerRow77_3 67 x)+(boundaryRePowerRow77_4 67 x)))))))+(((((boundaryRePowerRow77_5 67 x)+(((boundaryRePowerRow77_6 67 x)+(boundaryRePowerRow77_7 67 x)))))+(((boundaryRePowerRow77_8 67 x)+(((boundaryRePowerRow77_9 67 x)+(boundaryRePowerRow77_10 67 x)))))))))+(((((((boundaryRePowerRow77_11 67 x)+(((boundaryRePowerRow77_12 67 x)+(boundaryRePowerRow77_13 67 x)))))+(((boundaryRePowerRow77_14 67 x)+(((boundaryRePowerRow77_15 67 x)+(boundaryRePowerRow77_16 67 x)))))))+(((((boundaryRePowerRow77_17 67 x)+(((boundaryRePowerRow77_18 67 x)+(boundaryRePowerRow77_19 67 x)))))+(((boundaryRePowerRow77_20 67 x)+(((boundaryRePowerRow77_21 67 x)+(boundaryRePowerRow77_22 67 x)))))))))))+(((((((((boundaryImPowerRow77_0 67 x)+(boundaryImPowerRow77_1 67 x)))+(((boundaryImPowerRow77_2 67 x)+(((boundaryImPowerRow77_3 67 x)+(boundaryImPowerRow77_4 67 x)))))))+(((((boundaryImPowerRow77_5 67 x)+(((boundaryImPowerRow77_6 67 x)+(boundaryImPowerRow77_7 67 x)))))+(((boundaryImPowerRow77_8 67 x)+(((boundaryImPowerRow77_9 67 x)+(boundaryImPowerRow77_10 67 x)))))))))+(((((((boundaryImPowerRow77_11 67 x)+(((boundaryImPowerRow77_12 67 x)+(boundaryImPowerRow77_13 67 x)))))+(((boundaryImPowerRow77_14 67 x)+(((boundaryImPowerRow77_15 67 x)+(boundaryImPowerRow77_16 67 x)))))))+(((((boundaryImPowerRow77_17 67 x)+(((boundaryImPowerRow77_18 67 x)+(boundaryImPowerRow77_19 67 x)))))+(((boundaryImPowerRow77_20 67 x)+(((boundaryImPowerRow77_21 67 x)+(boundaryLowPowerRow77 67 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree67Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree67Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
