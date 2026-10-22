import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree32Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree32Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x))=c} := by

  have he : ((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x))=(boundaryRePowerRow77_0Degree32Norm x).val+(boundaryRePowerRow77_1Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree32Norm x).property (boundaryRePowerRow77_1Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree32Norm,boundaryRePowerRow77_1Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x))=c} := by

  have he : ((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x))=(boundaryRePowerRow77_3Degree32Norm x).val+(boundaryRePowerRow77_4Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree32Norm x).property (boundaryRePowerRow77_4Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree32Norm,boundaryRePowerRow77_4Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x))))=(boundaryRePowerRow77_2Degree32Norm x).val+(boundaryFullPowerDegree32Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree32Norm x).property (boundaryFullPowerDegree32Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree32Norm,boundaryFullPowerDegree32Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x))))))=(boundaryFullPowerDegree32Block0Norm x).val+(boundaryFullPowerDegree32Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block0Norm x).property (boundaryFullPowerDegree32Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block0Norm,boundaryFullPowerDegree32Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x))=c} := by

  have he : ((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x))=(boundaryRePowerRow77_6Degree32Norm x).val+(boundaryRePowerRow77_7Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree32Norm x).property (boundaryRePowerRow77_7Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree32Norm,boundaryRePowerRow77_7Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x))))=(boundaryRePowerRow77_5Degree32Norm x).val+(boundaryFullPowerDegree32Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree32Norm x).property (boundaryFullPowerDegree32Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree32Norm,boundaryFullPowerDegree32Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))=c} := by

  have he : ((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))=(boundaryRePowerRow77_9Degree32Norm x).val+(boundaryRePowerRow77_10Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree32Norm x).property (boundaryRePowerRow77_10Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree32Norm,boundaryRePowerRow77_10Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))))=(boundaryRePowerRow77_8Degree32Norm x).val+(boundaryFullPowerDegree32Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree32Norm x).property (boundaryFullPowerDegree32Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree32Norm,boundaryFullPowerDegree32Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))))))=(boundaryFullPowerDegree32Block5Norm x).val+(boundaryFullPowerDegree32Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block5Norm x).property (boundaryFullPowerDegree32Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block5Norm,boundaryFullPowerDegree32Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x))))))))=(boundaryFullPowerDegree32Block3Norm x).val+(boundaryFullPowerDegree32Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block3Norm x).property (boundaryFullPowerDegree32Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block3Norm,boundaryFullPowerDegree32Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x))=c} := by

  have he : ((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x))=(boundaryRePowerRow77_12Degree32Norm x).val+(boundaryRePowerRow77_13Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree32Norm x).property (boundaryRePowerRow77_13Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree32Norm,boundaryRePowerRow77_13Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x))))=(boundaryRePowerRow77_11Degree32Norm x).val+(boundaryFullPowerDegree32Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree32Norm x).property (boundaryFullPowerDegree32Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree32Norm,boundaryFullPowerDegree32Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x))=c} := by

  have he : ((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x))=(boundaryRePowerRow77_15Degree32Norm x).val+(boundaryRePowerRow77_16Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree32Norm x).property (boundaryRePowerRow77_16Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree32Norm,boundaryRePowerRow77_16Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x))))=(boundaryRePowerRow77_14Degree32Norm x).val+(boundaryFullPowerDegree32Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree32Norm x).property (boundaryFullPowerDegree32Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree32Norm,boundaryFullPowerDegree32Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x))))))=(boundaryFullPowerDegree32Block11Norm x).val+(boundaryFullPowerDegree32Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block11Norm x).property (boundaryFullPowerDegree32Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block11Norm,boundaryFullPowerDegree32Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x))=c} := by

  have he : ((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x))=(boundaryRePowerRow77_18Degree32Norm x).val+(boundaryRePowerRow77_19Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree32Norm x).property (boundaryRePowerRow77_19Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree32Norm,boundaryRePowerRow77_19Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x))))=(boundaryRePowerRow77_17Degree32Norm x).val+(boundaryFullPowerDegree32Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree32Norm x).property (boundaryFullPowerDegree32Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree32Norm,boundaryFullPowerDegree32Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))=c} := by

  have he : ((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))=(boundaryRePowerRow77_21Degree32Norm x).val+(boundaryRePowerRow77_22Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree32Norm x).property (boundaryRePowerRow77_22Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree32Norm,boundaryRePowerRow77_22Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))=(boundaryRePowerRow77_20Degree32Norm x).val+(boundaryFullPowerDegree32Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree32Norm x).property (boundaryFullPowerDegree32Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree32Norm,boundaryFullPowerDegree32Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))))=(boundaryFullPowerDegree32Block16Norm x).val+(boundaryFullPowerDegree32Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block16Norm x).property (boundaryFullPowerDegree32Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block16Norm,boundaryFullPowerDegree32Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))))))=(boundaryFullPowerDegree32Block14Norm x).val+(boundaryFullPowerDegree32Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block14Norm x).property (boundaryFullPowerDegree32Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block14Norm,boundaryFullPowerDegree32Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x)))))))))+(((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x)))))))))+(((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x))))))))))=(boundaryFullPowerDegree32Block9Norm x).val+(boundaryFullPowerDegree32Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block9Norm x).property (boundaryFullPowerDegree32Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block9Norm,boundaryFullPowerDegree32Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x))=c} := by

  have he : ((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x))=(boundaryImPowerRow77_0Degree32Norm x).val+(boundaryImPowerRow77_1Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree32Norm x).property (boundaryImPowerRow77_1Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree32Norm,boundaryImPowerRow77_1Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x))=c} := by

  have he : ((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x))=(boundaryImPowerRow77_3Degree32Norm x).val+(boundaryImPowerRow77_4Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree32Norm x).property (boundaryImPowerRow77_4Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree32Norm,boundaryImPowerRow77_4Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x))))=(boundaryImPowerRow77_2Degree32Norm x).val+(boundaryFullPowerDegree32Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree32Norm x).property (boundaryFullPowerDegree32Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree32Norm,boundaryFullPowerDegree32Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x))))))=(boundaryFullPowerDegree32Block22Norm x).val+(boundaryFullPowerDegree32Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block22Norm x).property (boundaryFullPowerDegree32Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block22Norm,boundaryFullPowerDegree32Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x))=c} := by

  have he : ((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x))=(boundaryImPowerRow77_6Degree32Norm x).val+(boundaryImPowerRow77_7Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree32Norm x).property (boundaryImPowerRow77_7Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree32Norm,boundaryImPowerRow77_7Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x))))=(boundaryImPowerRow77_5Degree32Norm x).val+(boundaryFullPowerDegree32Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree32Norm x).property (boundaryFullPowerDegree32Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree32Norm,boundaryFullPowerDegree32Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))=c} := by

  have he : ((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))=(boundaryImPowerRow77_9Degree32Norm x).val+(boundaryImPowerRow77_10Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree32Norm x).property (boundaryImPowerRow77_10Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree32Norm,boundaryImPowerRow77_10Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))))=(boundaryImPowerRow77_8Degree32Norm x).val+(boundaryFullPowerDegree32Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree32Norm x).property (boundaryFullPowerDegree32Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree32Norm,boundaryFullPowerDegree32Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))))))=(boundaryFullPowerDegree32Block27Norm x).val+(boundaryFullPowerDegree32Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block27Norm x).property (boundaryFullPowerDegree32Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block27Norm,boundaryFullPowerDegree32Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x))))))))=(boundaryFullPowerDegree32Block25Norm x).val+(boundaryFullPowerDegree32Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block25Norm x).property (boundaryFullPowerDegree32Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block25Norm,boundaryFullPowerDegree32Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x))=c} := by

  have he : ((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x))=(boundaryImPowerRow77_12Degree32Norm x).val+(boundaryImPowerRow77_13Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree32Norm x).property (boundaryImPowerRow77_13Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree32Norm,boundaryImPowerRow77_13Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x))))=(boundaryImPowerRow77_11Degree32Norm x).val+(boundaryFullPowerDegree32Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree32Norm x).property (boundaryFullPowerDegree32Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree32Norm,boundaryFullPowerDegree32Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x))=c} := by

  have he : ((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x))=(boundaryImPowerRow77_15Degree32Norm x).val+(boundaryImPowerRow77_16Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree32Norm x).property (boundaryImPowerRow77_16Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree32Norm,boundaryImPowerRow77_16Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x))))=(boundaryImPowerRow77_14Degree32Norm x).val+(boundaryFullPowerDegree32Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree32Norm x).property (boundaryFullPowerDegree32Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree32Norm,boundaryFullPowerDegree32Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x))))))=(boundaryFullPowerDegree32Block33Norm x).val+(boundaryFullPowerDegree32Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block33Norm x).property (boundaryFullPowerDegree32Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block33Norm,boundaryFullPowerDegree32Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x))=c} := by

  have he : ((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x))=(boundaryImPowerRow77_18Degree32Norm x).val+(boundaryImPowerRow77_19Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree32Norm x).property (boundaryImPowerRow77_19Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree32Norm,boundaryImPowerRow77_19Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x))))=(boundaryImPowerRow77_17Degree32Norm x).val+(boundaryFullPowerDegree32Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree32Norm x).property (boundaryFullPowerDegree32Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree32Norm,boundaryFullPowerDegree32Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))=c} := by

  have he : ((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))=(boundaryImPowerRow77_21Degree32Norm x).val+(boundaryLowPowerRow77Degree32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree32Norm x).property (boundaryLowPowerRow77Degree32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree32Norm,boundaryLowPowerRow77Degree32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))=(boundaryImPowerRow77_20Degree32Norm x).val+(boundaryFullPowerDegree32Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree32Norm x).property (boundaryFullPowerDegree32Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree32Norm,boundaryFullPowerDegree32Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))=(boundaryFullPowerDegree32Block38Norm x).val+(boundaryFullPowerDegree32Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block38Norm x).property (boundaryFullPowerDegree32Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block38Norm,boundaryFullPowerDegree32Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))))=(boundaryFullPowerDegree32Block36Norm x).val+(boundaryFullPowerDegree32Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block36Norm x).property (boundaryFullPowerDegree32Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block36Norm,boundaryFullPowerDegree32Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x)))))))))+(((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x)))))))))+(((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))))))=(boundaryFullPowerDegree32Block31Norm x).val+(boundaryFullPowerDegree32Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block31Norm x).property (boundaryFullPowerDegree32Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block31Norm,boundaryFullPowerDegree32Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree32Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x)))))))))+(((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x)))))))))))+(((((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x)))))))))+(((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x)))))))))+(((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x)))))))))))+(((((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x)))))))))+(((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x))))))))))))=(boundaryFullPowerDegree32Block21Norm x).val+(boundaryFullPowerDegree32Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree32Block21Norm x).property (boundaryFullPowerDegree32Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block21Norm,boundaryFullPowerDegree32Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree32Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 32 x=c} := by

  have he0 : boundaryFullPowerRow77 32 x=((((((((((boundaryRePowerRow77_0 32 x)+(boundaryRePowerRow77_1 32 x)))+(((boundaryRePowerRow77_2 32 x)+(((boundaryRePowerRow77_3 32 x)+(boundaryRePowerRow77_4 32 x)))))))+(((((boundaryRePowerRow77_5 32 x)+(((boundaryRePowerRow77_6 32 x)+(boundaryRePowerRow77_7 32 x)))))+(((boundaryRePowerRow77_8 32 x)+(((boundaryRePowerRow77_9 32 x)+(boundaryRePowerRow77_10 32 x)))))))))+(((((((boundaryRePowerRow77_11 32 x)+(((boundaryRePowerRow77_12 32 x)+(boundaryRePowerRow77_13 32 x)))))+(((boundaryRePowerRow77_14 32 x)+(((boundaryRePowerRow77_15 32 x)+(boundaryRePowerRow77_16 32 x)))))))+(((((boundaryRePowerRow77_17 32 x)+(((boundaryRePowerRow77_18 32 x)+(boundaryRePowerRow77_19 32 x)))))+(((boundaryRePowerRow77_20 32 x)+(((boundaryRePowerRow77_21 32 x)+(boundaryRePowerRow77_22 32 x)))))))))))+(((((((((boundaryImPowerRow77_0 32 x)+(boundaryImPowerRow77_1 32 x)))+(((boundaryImPowerRow77_2 32 x)+(((boundaryImPowerRow77_3 32 x)+(boundaryImPowerRow77_4 32 x)))))))+(((((boundaryImPowerRow77_5 32 x)+(((boundaryImPowerRow77_6 32 x)+(boundaryImPowerRow77_7 32 x)))))+(((boundaryImPowerRow77_8 32 x)+(((boundaryImPowerRow77_9 32 x)+(boundaryImPowerRow77_10 32 x)))))))))+(((((((boundaryImPowerRow77_11 32 x)+(((boundaryImPowerRow77_12 32 x)+(boundaryImPowerRow77_13 32 x)))))+(((boundaryImPowerRow77_14 32 x)+(((boundaryImPowerRow77_15 32 x)+(boundaryImPowerRow77_16 32 x)))))))+(((((boundaryImPowerRow77_17 32 x)+(((boundaryImPowerRow77_18 32 x)+(boundaryImPowerRow77_19 32 x)))))+(((boundaryImPowerRow77_20 32 x)+(((boundaryImPowerRow77_21 32 x)+(boundaryLowPowerRow77 32 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree32Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree32Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
