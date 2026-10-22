import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree74Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree74Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x))=c} := by

  have he : ((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x))=(boundaryRePowerRow77_0Degree74Norm x).val+(boundaryRePowerRow77_1Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree74Norm x).property (boundaryRePowerRow77_1Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree74Norm,boundaryRePowerRow77_1Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x))=c} := by

  have he : ((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x))=(boundaryRePowerRow77_3Degree74Norm x).val+(boundaryRePowerRow77_4Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree74Norm x).property (boundaryRePowerRow77_4Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree74Norm,boundaryRePowerRow77_4Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x))))=(boundaryRePowerRow77_2Degree74Norm x).val+(boundaryFullPowerDegree74Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree74Norm x).property (boundaryFullPowerDegree74Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree74Norm,boundaryFullPowerDegree74Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x))))))=(boundaryFullPowerDegree74Block0Norm x).val+(boundaryFullPowerDegree74Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block0Norm x).property (boundaryFullPowerDegree74Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block0Norm,boundaryFullPowerDegree74Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x))=c} := by

  have he : ((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x))=(boundaryRePowerRow77_6Degree74Norm x).val+(boundaryRePowerRow77_7Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree74Norm x).property (boundaryRePowerRow77_7Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree74Norm,boundaryRePowerRow77_7Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x))))=(boundaryRePowerRow77_5Degree74Norm x).val+(boundaryFullPowerDegree74Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree74Norm x).property (boundaryFullPowerDegree74Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree74Norm,boundaryFullPowerDegree74Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))=c} := by

  have he : ((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))=(boundaryRePowerRow77_9Degree74Norm x).val+(boundaryRePowerRow77_10Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree74Norm x).property (boundaryRePowerRow77_10Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree74Norm,boundaryRePowerRow77_10Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))))=(boundaryRePowerRow77_8Degree74Norm x).val+(boundaryFullPowerDegree74Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree74Norm x).property (boundaryFullPowerDegree74Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree74Norm,boundaryFullPowerDegree74Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))))))=(boundaryFullPowerDegree74Block5Norm x).val+(boundaryFullPowerDegree74Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block5Norm x).property (boundaryFullPowerDegree74Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block5Norm,boundaryFullPowerDegree74Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x))))))))=(boundaryFullPowerDegree74Block3Norm x).val+(boundaryFullPowerDegree74Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block3Norm x).property (boundaryFullPowerDegree74Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block3Norm,boundaryFullPowerDegree74Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x))=c} := by

  have he : ((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x))=(boundaryRePowerRow77_12Degree74Norm x).val+(boundaryRePowerRow77_13Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree74Norm x).property (boundaryRePowerRow77_13Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree74Norm,boundaryRePowerRow77_13Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x))))=(boundaryRePowerRow77_11Degree74Norm x).val+(boundaryFullPowerDegree74Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree74Norm x).property (boundaryFullPowerDegree74Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree74Norm,boundaryFullPowerDegree74Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x))=c} := by

  have he : ((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x))=(boundaryRePowerRow77_15Degree74Norm x).val+(boundaryRePowerRow77_16Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree74Norm x).property (boundaryRePowerRow77_16Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree74Norm,boundaryRePowerRow77_16Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x))))=(boundaryRePowerRow77_14Degree74Norm x).val+(boundaryFullPowerDegree74Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree74Norm x).property (boundaryFullPowerDegree74Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree74Norm,boundaryFullPowerDegree74Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x))))))=(boundaryFullPowerDegree74Block11Norm x).val+(boundaryFullPowerDegree74Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block11Norm x).property (boundaryFullPowerDegree74Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block11Norm,boundaryFullPowerDegree74Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x))=c} := by

  have he : ((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x))=(boundaryRePowerRow77_18Degree74Norm x).val+(boundaryRePowerRow77_19Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree74Norm x).property (boundaryRePowerRow77_19Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree74Norm,boundaryRePowerRow77_19Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x))))=(boundaryRePowerRow77_17Degree74Norm x).val+(boundaryFullPowerDegree74Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree74Norm x).property (boundaryFullPowerDegree74Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree74Norm,boundaryFullPowerDegree74Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))=c} := by

  have he : ((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))=(boundaryRePowerRow77_21Degree74Norm x).val+(boundaryRePowerRow77_22Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree74Norm x).property (boundaryRePowerRow77_22Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree74Norm,boundaryRePowerRow77_22Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))=(boundaryRePowerRow77_20Degree74Norm x).val+(boundaryFullPowerDegree74Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree74Norm x).property (boundaryFullPowerDegree74Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree74Norm,boundaryFullPowerDegree74Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))))=(boundaryFullPowerDegree74Block16Norm x).val+(boundaryFullPowerDegree74Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block16Norm x).property (boundaryFullPowerDegree74Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block16Norm,boundaryFullPowerDegree74Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))))))=(boundaryFullPowerDegree74Block14Norm x).val+(boundaryFullPowerDegree74Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block14Norm x).property (boundaryFullPowerDegree74Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block14Norm,boundaryFullPowerDegree74Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x)))))))))+(((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x)))))))))+(((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x))))))))))=(boundaryFullPowerDegree74Block9Norm x).val+(boundaryFullPowerDegree74Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block9Norm x).property (boundaryFullPowerDegree74Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block9Norm,boundaryFullPowerDegree74Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x))=c} := by

  have he : ((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x))=(boundaryImPowerRow77_0Degree74Norm x).val+(boundaryImPowerRow77_1Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree74Norm x).property (boundaryImPowerRow77_1Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree74Norm,boundaryImPowerRow77_1Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x))=c} := by

  have he : ((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x))=(boundaryImPowerRow77_3Degree74Norm x).val+(boundaryImPowerRow77_4Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree74Norm x).property (boundaryImPowerRow77_4Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree74Norm,boundaryImPowerRow77_4Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x))))=(boundaryImPowerRow77_2Degree74Norm x).val+(boundaryFullPowerDegree74Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree74Norm x).property (boundaryFullPowerDegree74Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree74Norm,boundaryFullPowerDegree74Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x))))))=(boundaryFullPowerDegree74Block22Norm x).val+(boundaryFullPowerDegree74Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block22Norm x).property (boundaryFullPowerDegree74Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block22Norm,boundaryFullPowerDegree74Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x))=c} := by

  have he : ((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x))=(boundaryImPowerRow77_6Degree74Norm x).val+(boundaryImPowerRow77_7Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree74Norm x).property (boundaryImPowerRow77_7Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree74Norm,boundaryImPowerRow77_7Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x))))=(boundaryImPowerRow77_5Degree74Norm x).val+(boundaryFullPowerDegree74Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree74Norm x).property (boundaryFullPowerDegree74Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree74Norm,boundaryFullPowerDegree74Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))=c} := by

  have he : ((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))=(boundaryImPowerRow77_9Degree74Norm x).val+(boundaryImPowerRow77_10Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree74Norm x).property (boundaryImPowerRow77_10Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree74Norm,boundaryImPowerRow77_10Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))))=(boundaryImPowerRow77_8Degree74Norm x).val+(boundaryFullPowerDegree74Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree74Norm x).property (boundaryFullPowerDegree74Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree74Norm,boundaryFullPowerDegree74Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))))))=(boundaryFullPowerDegree74Block27Norm x).val+(boundaryFullPowerDegree74Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block27Norm x).property (boundaryFullPowerDegree74Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block27Norm,boundaryFullPowerDegree74Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x))))))))=(boundaryFullPowerDegree74Block25Norm x).val+(boundaryFullPowerDegree74Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block25Norm x).property (boundaryFullPowerDegree74Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block25Norm,boundaryFullPowerDegree74Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x))=c} := by

  have he : ((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x))=(boundaryImPowerRow77_12Degree74Norm x).val+(boundaryImPowerRow77_13Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree74Norm x).property (boundaryImPowerRow77_13Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree74Norm,boundaryImPowerRow77_13Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x))))=(boundaryImPowerRow77_11Degree74Norm x).val+(boundaryFullPowerDegree74Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree74Norm x).property (boundaryFullPowerDegree74Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree74Norm,boundaryFullPowerDegree74Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x))=c} := by

  have he : ((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x))=(boundaryImPowerRow77_15Degree74Norm x).val+(boundaryImPowerRow77_16Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree74Norm x).property (boundaryImPowerRow77_16Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree74Norm,boundaryImPowerRow77_16Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x))))=(boundaryImPowerRow77_14Degree74Norm x).val+(boundaryFullPowerDegree74Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree74Norm x).property (boundaryFullPowerDegree74Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree74Norm,boundaryFullPowerDegree74Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x))))))=(boundaryFullPowerDegree74Block33Norm x).val+(boundaryFullPowerDegree74Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block33Norm x).property (boundaryFullPowerDegree74Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block33Norm,boundaryFullPowerDegree74Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x))=c} := by

  have he : ((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x))=(boundaryImPowerRow77_18Degree74Norm x).val+(boundaryImPowerRow77_19Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree74Norm x).property (boundaryImPowerRow77_19Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree74Norm,boundaryImPowerRow77_19Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x))))=(boundaryImPowerRow77_17Degree74Norm x).val+(boundaryFullPowerDegree74Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree74Norm x).property (boundaryFullPowerDegree74Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree74Norm,boundaryFullPowerDegree74Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))=c} := by

  have he : ((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))=(boundaryImPowerRow77_21Degree74Norm x).val+(boundaryLowPowerRow77Degree74Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree74Norm x).property (boundaryLowPowerRow77Degree74Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree74Norm,boundaryLowPowerRow77Degree74Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))=(boundaryImPowerRow77_20Degree74Norm x).val+(boundaryFullPowerDegree74Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree74Norm x).property (boundaryFullPowerDegree74Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree74Norm,boundaryFullPowerDegree74Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))=(boundaryFullPowerDegree74Block38Norm x).val+(boundaryFullPowerDegree74Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block38Norm x).property (boundaryFullPowerDegree74Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block38Norm,boundaryFullPowerDegree74Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))))=(boundaryFullPowerDegree74Block36Norm x).val+(boundaryFullPowerDegree74Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block36Norm x).property (boundaryFullPowerDegree74Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block36Norm,boundaryFullPowerDegree74Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x)))))))))+(((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x)))))))))+(((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))))))=(boundaryFullPowerDegree74Block31Norm x).val+(boundaryFullPowerDegree74Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block31Norm x).property (boundaryFullPowerDegree74Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block31Norm,boundaryFullPowerDegree74Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree74Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x)))))))))+(((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x)))))))))))+(((((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x)))))))))+(((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x)))))))))+(((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x)))))))))))+(((((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x)))))))))+(((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x))))))))))))=(boundaryFullPowerDegree74Block21Norm x).val+(boundaryFullPowerDegree74Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree74Block21Norm x).property (boundaryFullPowerDegree74Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block21Norm,boundaryFullPowerDegree74Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree74Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 74 x=c} := by

  have he0 : boundaryFullPowerRow77 74 x=((((((((((boundaryRePowerRow77_0 74 x)+(boundaryRePowerRow77_1 74 x)))+(((boundaryRePowerRow77_2 74 x)+(((boundaryRePowerRow77_3 74 x)+(boundaryRePowerRow77_4 74 x)))))))+(((((boundaryRePowerRow77_5 74 x)+(((boundaryRePowerRow77_6 74 x)+(boundaryRePowerRow77_7 74 x)))))+(((boundaryRePowerRow77_8 74 x)+(((boundaryRePowerRow77_9 74 x)+(boundaryRePowerRow77_10 74 x)))))))))+(((((((boundaryRePowerRow77_11 74 x)+(((boundaryRePowerRow77_12 74 x)+(boundaryRePowerRow77_13 74 x)))))+(((boundaryRePowerRow77_14 74 x)+(((boundaryRePowerRow77_15 74 x)+(boundaryRePowerRow77_16 74 x)))))))+(((((boundaryRePowerRow77_17 74 x)+(((boundaryRePowerRow77_18 74 x)+(boundaryRePowerRow77_19 74 x)))))+(((boundaryRePowerRow77_20 74 x)+(((boundaryRePowerRow77_21 74 x)+(boundaryRePowerRow77_22 74 x)))))))))))+(((((((((boundaryImPowerRow77_0 74 x)+(boundaryImPowerRow77_1 74 x)))+(((boundaryImPowerRow77_2 74 x)+(((boundaryImPowerRow77_3 74 x)+(boundaryImPowerRow77_4 74 x)))))))+(((((boundaryImPowerRow77_5 74 x)+(((boundaryImPowerRow77_6 74 x)+(boundaryImPowerRow77_7 74 x)))))+(((boundaryImPowerRow77_8 74 x)+(((boundaryImPowerRow77_9 74 x)+(boundaryImPowerRow77_10 74 x)))))))))+(((((((boundaryImPowerRow77_11 74 x)+(((boundaryImPowerRow77_12 74 x)+(boundaryImPowerRow77_13 74 x)))))+(((boundaryImPowerRow77_14 74 x)+(((boundaryImPowerRow77_15 74 x)+(boundaryImPowerRow77_16 74 x)))))))+(((((boundaryImPowerRow77_17 74 x)+(((boundaryImPowerRow77_18 74 x)+(boundaryImPowerRow77_19 74 x)))))+(((boundaryImPowerRow77_20 74 x)+(((boundaryImPowerRow77_21 74 x)+(boundaryLowPowerRow77 74 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree74Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree74Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
