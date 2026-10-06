import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree29Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree29Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x))=c} := by

  have he : ((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x))=(boundaryRePowerRow77_0Degree29Norm x).val+(boundaryRePowerRow77_1Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree29Norm x).property (boundaryRePowerRow77_1Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree29Norm,boundaryRePowerRow77_1Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x))=c} := by

  have he : ((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x))=(boundaryRePowerRow77_3Degree29Norm x).val+(boundaryRePowerRow77_4Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree29Norm x).property (boundaryRePowerRow77_4Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree29Norm,boundaryRePowerRow77_4Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x))))=(boundaryRePowerRow77_2Degree29Norm x).val+(boundaryFullPowerDegree29Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree29Norm x).property (boundaryFullPowerDegree29Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree29Norm,boundaryFullPowerDegree29Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x))))))=(boundaryFullPowerDegree29Block0Norm x).val+(boundaryFullPowerDegree29Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block0Norm x).property (boundaryFullPowerDegree29Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block0Norm,boundaryFullPowerDegree29Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x))=c} := by

  have he : ((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x))=(boundaryRePowerRow77_6Degree29Norm x).val+(boundaryRePowerRow77_7Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree29Norm x).property (boundaryRePowerRow77_7Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree29Norm,boundaryRePowerRow77_7Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x))))=(boundaryRePowerRow77_5Degree29Norm x).val+(boundaryFullPowerDegree29Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree29Norm x).property (boundaryFullPowerDegree29Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree29Norm,boundaryFullPowerDegree29Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))=c} := by

  have he : ((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))=(boundaryRePowerRow77_9Degree29Norm x).val+(boundaryRePowerRow77_10Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree29Norm x).property (boundaryRePowerRow77_10Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree29Norm,boundaryRePowerRow77_10Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))))=(boundaryRePowerRow77_8Degree29Norm x).val+(boundaryFullPowerDegree29Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree29Norm x).property (boundaryFullPowerDegree29Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree29Norm,boundaryFullPowerDegree29Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))))))=(boundaryFullPowerDegree29Block5Norm x).val+(boundaryFullPowerDegree29Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block5Norm x).property (boundaryFullPowerDegree29Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block5Norm,boundaryFullPowerDegree29Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x))))))))=(boundaryFullPowerDegree29Block3Norm x).val+(boundaryFullPowerDegree29Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block3Norm x).property (boundaryFullPowerDegree29Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block3Norm,boundaryFullPowerDegree29Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x))=c} := by

  have he : ((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x))=(boundaryRePowerRow77_12Degree29Norm x).val+(boundaryRePowerRow77_13Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree29Norm x).property (boundaryRePowerRow77_13Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree29Norm,boundaryRePowerRow77_13Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x))))=(boundaryRePowerRow77_11Degree29Norm x).val+(boundaryFullPowerDegree29Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree29Norm x).property (boundaryFullPowerDegree29Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree29Norm,boundaryFullPowerDegree29Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x))=c} := by

  have he : ((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x))=(boundaryRePowerRow77_15Degree29Norm x).val+(boundaryRePowerRow77_16Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree29Norm x).property (boundaryRePowerRow77_16Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree29Norm,boundaryRePowerRow77_16Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x))))=(boundaryRePowerRow77_14Degree29Norm x).val+(boundaryFullPowerDegree29Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree29Norm x).property (boundaryFullPowerDegree29Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree29Norm,boundaryFullPowerDegree29Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x))))))=(boundaryFullPowerDegree29Block11Norm x).val+(boundaryFullPowerDegree29Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block11Norm x).property (boundaryFullPowerDegree29Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block11Norm,boundaryFullPowerDegree29Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x))=c} := by

  have he : ((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x))=(boundaryRePowerRow77_18Degree29Norm x).val+(boundaryRePowerRow77_19Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree29Norm x).property (boundaryRePowerRow77_19Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree29Norm,boundaryRePowerRow77_19Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x))))=(boundaryRePowerRow77_17Degree29Norm x).val+(boundaryFullPowerDegree29Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree29Norm x).property (boundaryFullPowerDegree29Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree29Norm,boundaryFullPowerDegree29Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))=c} := by

  have he : ((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))=(boundaryRePowerRow77_21Degree29Norm x).val+(boundaryRePowerRow77_22Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree29Norm x).property (boundaryRePowerRow77_22Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree29Norm,boundaryRePowerRow77_22Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))=(boundaryRePowerRow77_20Degree29Norm x).val+(boundaryFullPowerDegree29Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree29Norm x).property (boundaryFullPowerDegree29Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree29Norm,boundaryFullPowerDegree29Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))))=(boundaryFullPowerDegree29Block16Norm x).val+(boundaryFullPowerDegree29Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block16Norm x).property (boundaryFullPowerDegree29Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block16Norm,boundaryFullPowerDegree29Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))))))=(boundaryFullPowerDegree29Block14Norm x).val+(boundaryFullPowerDegree29Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block14Norm x).property (boundaryFullPowerDegree29Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block14Norm,boundaryFullPowerDegree29Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x)))))))))+(((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x)))))))))+(((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x))))))))))=(boundaryFullPowerDegree29Block9Norm x).val+(boundaryFullPowerDegree29Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block9Norm x).property (boundaryFullPowerDegree29Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block9Norm,boundaryFullPowerDegree29Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x))=c} := by

  have he : ((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x))=(boundaryImPowerRow77_0Degree29Norm x).val+(boundaryImPowerRow77_1Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree29Norm x).property (boundaryImPowerRow77_1Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree29Norm,boundaryImPowerRow77_1Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x))=c} := by

  have he : ((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x))=(boundaryImPowerRow77_3Degree29Norm x).val+(boundaryImPowerRow77_4Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree29Norm x).property (boundaryImPowerRow77_4Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree29Norm,boundaryImPowerRow77_4Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x))))=(boundaryImPowerRow77_2Degree29Norm x).val+(boundaryFullPowerDegree29Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree29Norm x).property (boundaryFullPowerDegree29Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree29Norm,boundaryFullPowerDegree29Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x))))))=(boundaryFullPowerDegree29Block22Norm x).val+(boundaryFullPowerDegree29Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block22Norm x).property (boundaryFullPowerDegree29Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block22Norm,boundaryFullPowerDegree29Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x))=c} := by

  have he : ((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x))=(boundaryImPowerRow77_6Degree29Norm x).val+(boundaryImPowerRow77_7Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree29Norm x).property (boundaryImPowerRow77_7Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree29Norm,boundaryImPowerRow77_7Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x))))=(boundaryImPowerRow77_5Degree29Norm x).val+(boundaryFullPowerDegree29Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree29Norm x).property (boundaryFullPowerDegree29Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree29Norm,boundaryFullPowerDegree29Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))=c} := by

  have he : ((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))=(boundaryImPowerRow77_9Degree29Norm x).val+(boundaryImPowerRow77_10Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree29Norm x).property (boundaryImPowerRow77_10Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree29Norm,boundaryImPowerRow77_10Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))))=(boundaryImPowerRow77_8Degree29Norm x).val+(boundaryFullPowerDegree29Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree29Norm x).property (boundaryFullPowerDegree29Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree29Norm,boundaryFullPowerDegree29Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))))))=(boundaryFullPowerDegree29Block27Norm x).val+(boundaryFullPowerDegree29Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block27Norm x).property (boundaryFullPowerDegree29Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block27Norm,boundaryFullPowerDegree29Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x))))))))=(boundaryFullPowerDegree29Block25Norm x).val+(boundaryFullPowerDegree29Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block25Norm x).property (boundaryFullPowerDegree29Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block25Norm,boundaryFullPowerDegree29Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x))=c} := by

  have he : ((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x))=(boundaryImPowerRow77_12Degree29Norm x).val+(boundaryImPowerRow77_13Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree29Norm x).property (boundaryImPowerRow77_13Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree29Norm,boundaryImPowerRow77_13Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x))))=(boundaryImPowerRow77_11Degree29Norm x).val+(boundaryFullPowerDegree29Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree29Norm x).property (boundaryFullPowerDegree29Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree29Norm,boundaryFullPowerDegree29Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x))=c} := by

  have he : ((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x))=(boundaryImPowerRow77_15Degree29Norm x).val+(boundaryImPowerRow77_16Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree29Norm x).property (boundaryImPowerRow77_16Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree29Norm,boundaryImPowerRow77_16Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x))))=(boundaryImPowerRow77_14Degree29Norm x).val+(boundaryFullPowerDegree29Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree29Norm x).property (boundaryFullPowerDegree29Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree29Norm,boundaryFullPowerDegree29Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x))))))=(boundaryFullPowerDegree29Block33Norm x).val+(boundaryFullPowerDegree29Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block33Norm x).property (boundaryFullPowerDegree29Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block33Norm,boundaryFullPowerDegree29Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x))=c} := by

  have he : ((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x))=(boundaryImPowerRow77_18Degree29Norm x).val+(boundaryImPowerRow77_19Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree29Norm x).property (boundaryImPowerRow77_19Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree29Norm,boundaryImPowerRow77_19Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x))))=(boundaryImPowerRow77_17Degree29Norm x).val+(boundaryFullPowerDegree29Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree29Norm x).property (boundaryFullPowerDegree29Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree29Norm,boundaryFullPowerDegree29Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))=c} := by

  have he : ((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))=(boundaryImPowerRow77_21Degree29Norm x).val+(boundaryLowPowerRow77Degree29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree29Norm x).property (boundaryLowPowerRow77Degree29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree29Norm,boundaryLowPowerRow77Degree29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))=(boundaryImPowerRow77_20Degree29Norm x).val+(boundaryFullPowerDegree29Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree29Norm x).property (boundaryFullPowerDegree29Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree29Norm,boundaryFullPowerDegree29Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))=(boundaryFullPowerDegree29Block38Norm x).val+(boundaryFullPowerDegree29Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block38Norm x).property (boundaryFullPowerDegree29Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block38Norm,boundaryFullPowerDegree29Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))))=(boundaryFullPowerDegree29Block36Norm x).val+(boundaryFullPowerDegree29Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block36Norm x).property (boundaryFullPowerDegree29Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block36Norm,boundaryFullPowerDegree29Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x)))))))))+(((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x)))))))))+(((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))))))=(boundaryFullPowerDegree29Block31Norm x).val+(boundaryFullPowerDegree29Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block31Norm x).property (boundaryFullPowerDegree29Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block31Norm,boundaryFullPowerDegree29Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree29Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x)))))))))+(((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x)))))))))))+(((((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x)))))))))+(((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x)))))))))+(((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x)))))))))))+(((((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x)))))))))+(((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x))))))))))))=(boundaryFullPowerDegree29Block21Norm x).val+(boundaryFullPowerDegree29Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree29Block21Norm x).property (boundaryFullPowerDegree29Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block21Norm,boundaryFullPowerDegree29Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree29Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 29 x=c} := by

  have he0 : boundaryFullPowerRow77 29 x=((((((((((boundaryRePowerRow77_0 29 x)+(boundaryRePowerRow77_1 29 x)))+(((boundaryRePowerRow77_2 29 x)+(((boundaryRePowerRow77_3 29 x)+(boundaryRePowerRow77_4 29 x)))))))+(((((boundaryRePowerRow77_5 29 x)+(((boundaryRePowerRow77_6 29 x)+(boundaryRePowerRow77_7 29 x)))))+(((boundaryRePowerRow77_8 29 x)+(((boundaryRePowerRow77_9 29 x)+(boundaryRePowerRow77_10 29 x)))))))))+(((((((boundaryRePowerRow77_11 29 x)+(((boundaryRePowerRow77_12 29 x)+(boundaryRePowerRow77_13 29 x)))))+(((boundaryRePowerRow77_14 29 x)+(((boundaryRePowerRow77_15 29 x)+(boundaryRePowerRow77_16 29 x)))))))+(((((boundaryRePowerRow77_17 29 x)+(((boundaryRePowerRow77_18 29 x)+(boundaryRePowerRow77_19 29 x)))))+(((boundaryRePowerRow77_20 29 x)+(((boundaryRePowerRow77_21 29 x)+(boundaryRePowerRow77_22 29 x)))))))))))+(((((((((boundaryImPowerRow77_0 29 x)+(boundaryImPowerRow77_1 29 x)))+(((boundaryImPowerRow77_2 29 x)+(((boundaryImPowerRow77_3 29 x)+(boundaryImPowerRow77_4 29 x)))))))+(((((boundaryImPowerRow77_5 29 x)+(((boundaryImPowerRow77_6 29 x)+(boundaryImPowerRow77_7 29 x)))))+(((boundaryImPowerRow77_8 29 x)+(((boundaryImPowerRow77_9 29 x)+(boundaryImPowerRow77_10 29 x)))))))))+(((((((boundaryImPowerRow77_11 29 x)+(((boundaryImPowerRow77_12 29 x)+(boundaryImPowerRow77_13 29 x)))))+(((boundaryImPowerRow77_14 29 x)+(((boundaryImPowerRow77_15 29 x)+(boundaryImPowerRow77_16 29 x)))))))+(((((boundaryImPowerRow77_17 29 x)+(((boundaryImPowerRow77_18 29 x)+(boundaryImPowerRow77_19 29 x)))))+(((boundaryImPowerRow77_20 29 x)+(((boundaryImPowerRow77_21 29 x)+(boundaryLowPowerRow77 29 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree29Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree29Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
