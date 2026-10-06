import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree8Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree8Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x))=c} := by

  have he : ((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x))=(boundaryRePowerRow77_0Degree8Norm x).val+(boundaryRePowerRow77_1Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree8Norm x).property (boundaryRePowerRow77_1Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree8Norm,boundaryRePowerRow77_1Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x))=c} := by

  have he : ((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x))=(boundaryRePowerRow77_3Degree8Norm x).val+(boundaryRePowerRow77_4Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree8Norm x).property (boundaryRePowerRow77_4Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree8Norm,boundaryRePowerRow77_4Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x))))=(boundaryRePowerRow77_2Degree8Norm x).val+(boundaryFullPowerDegree8Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree8Norm x).property (boundaryFullPowerDegree8Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree8Norm,boundaryFullPowerDegree8Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x))))))=(boundaryFullPowerDegree8Block0Norm x).val+(boundaryFullPowerDegree8Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block0Norm x).property (boundaryFullPowerDegree8Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block0Norm,boundaryFullPowerDegree8Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x))=c} := by

  have he : ((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x))=(boundaryRePowerRow77_6Degree8Norm x).val+(boundaryRePowerRow77_7Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree8Norm x).property (boundaryRePowerRow77_7Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree8Norm,boundaryRePowerRow77_7Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x))))=(boundaryRePowerRow77_5Degree8Norm x).val+(boundaryFullPowerDegree8Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree8Norm x).property (boundaryFullPowerDegree8Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree8Norm,boundaryFullPowerDegree8Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))=c} := by

  have he : ((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))=(boundaryRePowerRow77_9Degree8Norm x).val+(boundaryRePowerRow77_10Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree8Norm x).property (boundaryRePowerRow77_10Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree8Norm,boundaryRePowerRow77_10Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))))=(boundaryRePowerRow77_8Degree8Norm x).val+(boundaryFullPowerDegree8Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree8Norm x).property (boundaryFullPowerDegree8Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree8Norm,boundaryFullPowerDegree8Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))))))=(boundaryFullPowerDegree8Block5Norm x).val+(boundaryFullPowerDegree8Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block5Norm x).property (boundaryFullPowerDegree8Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block5Norm,boundaryFullPowerDegree8Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x))))))))=(boundaryFullPowerDegree8Block3Norm x).val+(boundaryFullPowerDegree8Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block3Norm x).property (boundaryFullPowerDegree8Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block3Norm,boundaryFullPowerDegree8Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x))=c} := by

  have he : ((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x))=(boundaryRePowerRow77_12Degree8Norm x).val+(boundaryRePowerRow77_13Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree8Norm x).property (boundaryRePowerRow77_13Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree8Norm,boundaryRePowerRow77_13Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x))))=(boundaryRePowerRow77_11Degree8Norm x).val+(boundaryFullPowerDegree8Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree8Norm x).property (boundaryFullPowerDegree8Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree8Norm,boundaryFullPowerDegree8Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x))=c} := by

  have he : ((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x))=(boundaryRePowerRow77_15Degree8Norm x).val+(boundaryRePowerRow77_16Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree8Norm x).property (boundaryRePowerRow77_16Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree8Norm,boundaryRePowerRow77_16Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x))))=(boundaryRePowerRow77_14Degree8Norm x).val+(boundaryFullPowerDegree8Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree8Norm x).property (boundaryFullPowerDegree8Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree8Norm,boundaryFullPowerDegree8Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x))))))=(boundaryFullPowerDegree8Block11Norm x).val+(boundaryFullPowerDegree8Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block11Norm x).property (boundaryFullPowerDegree8Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block11Norm,boundaryFullPowerDegree8Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x))=c} := by

  have he : ((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x))=(boundaryRePowerRow77_18Degree8Norm x).val+(boundaryRePowerRow77_19Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree8Norm x).property (boundaryRePowerRow77_19Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree8Norm,boundaryRePowerRow77_19Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x))))=(boundaryRePowerRow77_17Degree8Norm x).val+(boundaryFullPowerDegree8Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree8Norm x).property (boundaryFullPowerDegree8Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree8Norm,boundaryFullPowerDegree8Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))=c} := by

  have he : ((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))=(boundaryRePowerRow77_21Degree8Norm x).val+(boundaryRePowerRow77_22Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree8Norm x).property (boundaryRePowerRow77_22Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree8Norm,boundaryRePowerRow77_22Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))=(boundaryRePowerRow77_20Degree8Norm x).val+(boundaryFullPowerDegree8Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree8Norm x).property (boundaryFullPowerDegree8Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree8Norm,boundaryFullPowerDegree8Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))))=(boundaryFullPowerDegree8Block16Norm x).val+(boundaryFullPowerDegree8Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block16Norm x).property (boundaryFullPowerDegree8Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block16Norm,boundaryFullPowerDegree8Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))))))=(boundaryFullPowerDegree8Block14Norm x).val+(boundaryFullPowerDegree8Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block14Norm x).property (boundaryFullPowerDegree8Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block14Norm,boundaryFullPowerDegree8Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x)))))))))+(((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x)))))))))+(((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x))))))))))=(boundaryFullPowerDegree8Block9Norm x).val+(boundaryFullPowerDegree8Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block9Norm x).property (boundaryFullPowerDegree8Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block9Norm,boundaryFullPowerDegree8Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x))=c} := by

  have he : ((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x))=(boundaryImPowerRow77_0Degree8Norm x).val+(boundaryImPowerRow77_1Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree8Norm x).property (boundaryImPowerRow77_1Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree8Norm,boundaryImPowerRow77_1Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x))=c} := by

  have he : ((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x))=(boundaryImPowerRow77_3Degree8Norm x).val+(boundaryImPowerRow77_4Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree8Norm x).property (boundaryImPowerRow77_4Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree8Norm,boundaryImPowerRow77_4Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x))))=(boundaryImPowerRow77_2Degree8Norm x).val+(boundaryFullPowerDegree8Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree8Norm x).property (boundaryFullPowerDegree8Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree8Norm,boundaryFullPowerDegree8Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x))))))=(boundaryFullPowerDegree8Block22Norm x).val+(boundaryFullPowerDegree8Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block22Norm x).property (boundaryFullPowerDegree8Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block22Norm,boundaryFullPowerDegree8Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x))=c} := by

  have he : ((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x))=(boundaryImPowerRow77_6Degree8Norm x).val+(boundaryImPowerRow77_7Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree8Norm x).property (boundaryImPowerRow77_7Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree8Norm,boundaryImPowerRow77_7Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x))))=(boundaryImPowerRow77_5Degree8Norm x).val+(boundaryFullPowerDegree8Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree8Norm x).property (boundaryFullPowerDegree8Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree8Norm,boundaryFullPowerDegree8Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))=c} := by

  have he : ((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))=(boundaryImPowerRow77_9Degree8Norm x).val+(boundaryImPowerRow77_10Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree8Norm x).property (boundaryImPowerRow77_10Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree8Norm,boundaryImPowerRow77_10Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))))=(boundaryImPowerRow77_8Degree8Norm x).val+(boundaryFullPowerDegree8Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree8Norm x).property (boundaryFullPowerDegree8Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree8Norm,boundaryFullPowerDegree8Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))))))=(boundaryFullPowerDegree8Block27Norm x).val+(boundaryFullPowerDegree8Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block27Norm x).property (boundaryFullPowerDegree8Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block27Norm,boundaryFullPowerDegree8Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x))))))))=(boundaryFullPowerDegree8Block25Norm x).val+(boundaryFullPowerDegree8Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block25Norm x).property (boundaryFullPowerDegree8Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block25Norm,boundaryFullPowerDegree8Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x))=c} := by

  have he : ((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x))=(boundaryImPowerRow77_12Degree8Norm x).val+(boundaryImPowerRow77_13Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree8Norm x).property (boundaryImPowerRow77_13Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree8Norm,boundaryImPowerRow77_13Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x))))=(boundaryImPowerRow77_11Degree8Norm x).val+(boundaryFullPowerDegree8Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree8Norm x).property (boundaryFullPowerDegree8Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree8Norm,boundaryFullPowerDegree8Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x))=c} := by

  have he : ((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x))=(boundaryImPowerRow77_15Degree8Norm x).val+(boundaryImPowerRow77_16Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree8Norm x).property (boundaryImPowerRow77_16Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree8Norm,boundaryImPowerRow77_16Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x))))=(boundaryImPowerRow77_14Degree8Norm x).val+(boundaryFullPowerDegree8Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree8Norm x).property (boundaryFullPowerDegree8Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree8Norm,boundaryFullPowerDegree8Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x))))))=(boundaryFullPowerDegree8Block33Norm x).val+(boundaryFullPowerDegree8Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block33Norm x).property (boundaryFullPowerDegree8Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block33Norm,boundaryFullPowerDegree8Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x))=c} := by

  have he : ((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x))=(boundaryImPowerRow77_18Degree8Norm x).val+(boundaryImPowerRow77_19Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree8Norm x).property (boundaryImPowerRow77_19Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree8Norm,boundaryImPowerRow77_19Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x))))=(boundaryImPowerRow77_17Degree8Norm x).val+(boundaryFullPowerDegree8Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree8Norm x).property (boundaryFullPowerDegree8Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree8Norm,boundaryFullPowerDegree8Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))=c} := by

  have he : ((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))=(boundaryImPowerRow77_21Degree8Norm x).val+(boundaryLowPowerRow77Degree8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree8Norm x).property (boundaryLowPowerRow77Degree8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree8Norm,boundaryLowPowerRow77Degree8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))=(boundaryImPowerRow77_20Degree8Norm x).val+(boundaryFullPowerDegree8Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree8Norm x).property (boundaryFullPowerDegree8Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree8Norm,boundaryFullPowerDegree8Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))=(boundaryFullPowerDegree8Block38Norm x).val+(boundaryFullPowerDegree8Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block38Norm x).property (boundaryFullPowerDegree8Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block38Norm,boundaryFullPowerDegree8Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))))=(boundaryFullPowerDegree8Block36Norm x).val+(boundaryFullPowerDegree8Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block36Norm x).property (boundaryFullPowerDegree8Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block36Norm,boundaryFullPowerDegree8Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x)))))))))+(((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x)))))))))+(((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))))))=(boundaryFullPowerDegree8Block31Norm x).val+(boundaryFullPowerDegree8Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block31Norm x).property (boundaryFullPowerDegree8Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block31Norm,boundaryFullPowerDegree8Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree8Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x)))))))))+(((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x)))))))))))+(((((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x)))))))))+(((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x)))))))))+(((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x)))))))))))+(((((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x)))))))))+(((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x))))))))))))=(boundaryFullPowerDegree8Block21Norm x).val+(boundaryFullPowerDegree8Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree8Block21Norm x).property (boundaryFullPowerDegree8Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block21Norm,boundaryFullPowerDegree8Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree8Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 8 x=c} := by

  have he0 : boundaryFullPowerRow77 8 x=((((((((((boundaryRePowerRow77_0 8 x)+(boundaryRePowerRow77_1 8 x)))+(((boundaryRePowerRow77_2 8 x)+(((boundaryRePowerRow77_3 8 x)+(boundaryRePowerRow77_4 8 x)))))))+(((((boundaryRePowerRow77_5 8 x)+(((boundaryRePowerRow77_6 8 x)+(boundaryRePowerRow77_7 8 x)))))+(((boundaryRePowerRow77_8 8 x)+(((boundaryRePowerRow77_9 8 x)+(boundaryRePowerRow77_10 8 x)))))))))+(((((((boundaryRePowerRow77_11 8 x)+(((boundaryRePowerRow77_12 8 x)+(boundaryRePowerRow77_13 8 x)))))+(((boundaryRePowerRow77_14 8 x)+(((boundaryRePowerRow77_15 8 x)+(boundaryRePowerRow77_16 8 x)))))))+(((((boundaryRePowerRow77_17 8 x)+(((boundaryRePowerRow77_18 8 x)+(boundaryRePowerRow77_19 8 x)))))+(((boundaryRePowerRow77_20 8 x)+(((boundaryRePowerRow77_21 8 x)+(boundaryRePowerRow77_22 8 x)))))))))))+(((((((((boundaryImPowerRow77_0 8 x)+(boundaryImPowerRow77_1 8 x)))+(((boundaryImPowerRow77_2 8 x)+(((boundaryImPowerRow77_3 8 x)+(boundaryImPowerRow77_4 8 x)))))))+(((((boundaryImPowerRow77_5 8 x)+(((boundaryImPowerRow77_6 8 x)+(boundaryImPowerRow77_7 8 x)))))+(((boundaryImPowerRow77_8 8 x)+(((boundaryImPowerRow77_9 8 x)+(boundaryImPowerRow77_10 8 x)))))))))+(((((((boundaryImPowerRow77_11 8 x)+(((boundaryImPowerRow77_12 8 x)+(boundaryImPowerRow77_13 8 x)))))+(((boundaryImPowerRow77_14 8 x)+(((boundaryImPowerRow77_15 8 x)+(boundaryImPowerRow77_16 8 x)))))))+(((((boundaryImPowerRow77_17 8 x)+(((boundaryImPowerRow77_18 8 x)+(boundaryImPowerRow77_19 8 x)))))+(((boundaryImPowerRow77_20 8 x)+(((boundaryImPowerRow77_21 8 x)+(boundaryLowPowerRow77 8 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree8Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree8Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
