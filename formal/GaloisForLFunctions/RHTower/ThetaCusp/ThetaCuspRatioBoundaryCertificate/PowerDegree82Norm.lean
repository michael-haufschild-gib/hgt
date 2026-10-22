import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree82Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree82Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x))=c} := by

  have he : ((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x))=(boundaryRePowerRow77_0Degree82Norm x).val+(boundaryRePowerRow77_1Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree82Norm x).property (boundaryRePowerRow77_1Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree82Norm,boundaryRePowerRow77_1Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x))=c} := by

  have he : ((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x))=(boundaryRePowerRow77_3Degree82Norm x).val+(boundaryRePowerRow77_4Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree82Norm x).property (boundaryRePowerRow77_4Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree82Norm,boundaryRePowerRow77_4Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x))))=(boundaryRePowerRow77_2Degree82Norm x).val+(boundaryFullPowerDegree82Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree82Norm x).property (boundaryFullPowerDegree82Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree82Norm,boundaryFullPowerDegree82Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x))))))=(boundaryFullPowerDegree82Block0Norm x).val+(boundaryFullPowerDegree82Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block0Norm x).property (boundaryFullPowerDegree82Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block0Norm,boundaryFullPowerDegree82Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x))=c} := by

  have he : ((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x))=(boundaryRePowerRow77_6Degree82Norm x).val+(boundaryRePowerRow77_7Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree82Norm x).property (boundaryRePowerRow77_7Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree82Norm,boundaryRePowerRow77_7Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x))))=(boundaryRePowerRow77_5Degree82Norm x).val+(boundaryFullPowerDegree82Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree82Norm x).property (boundaryFullPowerDegree82Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree82Norm,boundaryFullPowerDegree82Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))=c} := by

  have he : ((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))=(boundaryRePowerRow77_9Degree82Norm x).val+(boundaryRePowerRow77_10Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree82Norm x).property (boundaryRePowerRow77_10Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree82Norm,boundaryRePowerRow77_10Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))))=(boundaryRePowerRow77_8Degree82Norm x).val+(boundaryFullPowerDegree82Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree82Norm x).property (boundaryFullPowerDegree82Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree82Norm,boundaryFullPowerDegree82Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))))))=(boundaryFullPowerDegree82Block5Norm x).val+(boundaryFullPowerDegree82Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block5Norm x).property (boundaryFullPowerDegree82Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block5Norm,boundaryFullPowerDegree82Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x))))))))=(boundaryFullPowerDegree82Block3Norm x).val+(boundaryFullPowerDegree82Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block3Norm x).property (boundaryFullPowerDegree82Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block3Norm,boundaryFullPowerDegree82Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x))=c} := by

  have he : ((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x))=(boundaryRePowerRow77_12Degree82Norm x).val+(boundaryRePowerRow77_13Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree82Norm x).property (boundaryRePowerRow77_13Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree82Norm,boundaryRePowerRow77_13Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x))))=(boundaryRePowerRow77_11Degree82Norm x).val+(boundaryFullPowerDegree82Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree82Norm x).property (boundaryFullPowerDegree82Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree82Norm,boundaryFullPowerDegree82Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x))=c} := by

  have he : ((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x))=(boundaryRePowerRow77_15Degree82Norm x).val+(boundaryRePowerRow77_16Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree82Norm x).property (boundaryRePowerRow77_16Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree82Norm,boundaryRePowerRow77_16Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x))))=(boundaryRePowerRow77_14Degree82Norm x).val+(boundaryFullPowerDegree82Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree82Norm x).property (boundaryFullPowerDegree82Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree82Norm,boundaryFullPowerDegree82Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x))))))=(boundaryFullPowerDegree82Block11Norm x).val+(boundaryFullPowerDegree82Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block11Norm x).property (boundaryFullPowerDegree82Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block11Norm,boundaryFullPowerDegree82Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x))=c} := by

  have he : ((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x))=(boundaryRePowerRow77_18Degree82Norm x).val+(boundaryRePowerRow77_19Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree82Norm x).property (boundaryRePowerRow77_19Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree82Norm,boundaryRePowerRow77_19Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x))))=(boundaryRePowerRow77_17Degree82Norm x).val+(boundaryFullPowerDegree82Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree82Norm x).property (boundaryFullPowerDegree82Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree82Norm,boundaryFullPowerDegree82Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))=c} := by

  have he : ((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))=(boundaryRePowerRow77_21Degree82Norm x).val+(boundaryRePowerRow77_22Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree82Norm x).property (boundaryRePowerRow77_22Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree82Norm,boundaryRePowerRow77_22Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))=(boundaryRePowerRow77_20Degree82Norm x).val+(boundaryFullPowerDegree82Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree82Norm x).property (boundaryFullPowerDegree82Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree82Norm,boundaryFullPowerDegree82Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))))=(boundaryFullPowerDegree82Block16Norm x).val+(boundaryFullPowerDegree82Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block16Norm x).property (boundaryFullPowerDegree82Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block16Norm,boundaryFullPowerDegree82Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))))))=(boundaryFullPowerDegree82Block14Norm x).val+(boundaryFullPowerDegree82Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block14Norm x).property (boundaryFullPowerDegree82Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block14Norm,boundaryFullPowerDegree82Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x)))))))))+(((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x)))))))))+(((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x))))))))))=(boundaryFullPowerDegree82Block9Norm x).val+(boundaryFullPowerDegree82Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block9Norm x).property (boundaryFullPowerDegree82Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block9Norm,boundaryFullPowerDegree82Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x))=c} := by

  have he : ((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x))=(boundaryImPowerRow77_0Degree82Norm x).val+(boundaryImPowerRow77_1Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree82Norm x).property (boundaryImPowerRow77_1Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree82Norm,boundaryImPowerRow77_1Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x))=c} := by

  have he : ((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x))=(boundaryImPowerRow77_3Degree82Norm x).val+(boundaryImPowerRow77_4Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree82Norm x).property (boundaryImPowerRow77_4Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree82Norm,boundaryImPowerRow77_4Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x))))=(boundaryImPowerRow77_2Degree82Norm x).val+(boundaryFullPowerDegree82Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree82Norm x).property (boundaryFullPowerDegree82Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree82Norm,boundaryFullPowerDegree82Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x))))))=(boundaryFullPowerDegree82Block22Norm x).val+(boundaryFullPowerDegree82Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block22Norm x).property (boundaryFullPowerDegree82Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block22Norm,boundaryFullPowerDegree82Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x))=c} := by

  have he : ((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x))=(boundaryImPowerRow77_6Degree82Norm x).val+(boundaryImPowerRow77_7Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree82Norm x).property (boundaryImPowerRow77_7Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree82Norm,boundaryImPowerRow77_7Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x))))=(boundaryImPowerRow77_5Degree82Norm x).val+(boundaryFullPowerDegree82Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree82Norm x).property (boundaryFullPowerDegree82Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree82Norm,boundaryFullPowerDegree82Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))=c} := by

  have he : ((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))=(boundaryImPowerRow77_9Degree82Norm x).val+(boundaryImPowerRow77_10Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree82Norm x).property (boundaryImPowerRow77_10Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree82Norm,boundaryImPowerRow77_10Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))))=(boundaryImPowerRow77_8Degree82Norm x).val+(boundaryFullPowerDegree82Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree82Norm x).property (boundaryFullPowerDegree82Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree82Norm,boundaryFullPowerDegree82Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))))))=(boundaryFullPowerDegree82Block27Norm x).val+(boundaryFullPowerDegree82Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block27Norm x).property (boundaryFullPowerDegree82Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block27Norm,boundaryFullPowerDegree82Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x))))))))=(boundaryFullPowerDegree82Block25Norm x).val+(boundaryFullPowerDegree82Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block25Norm x).property (boundaryFullPowerDegree82Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block25Norm,boundaryFullPowerDegree82Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x))=c} := by

  have he : ((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x))=(boundaryImPowerRow77_12Degree82Norm x).val+(boundaryImPowerRow77_13Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree82Norm x).property (boundaryImPowerRow77_13Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree82Norm,boundaryImPowerRow77_13Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x))))=(boundaryImPowerRow77_11Degree82Norm x).val+(boundaryFullPowerDegree82Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree82Norm x).property (boundaryFullPowerDegree82Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree82Norm,boundaryFullPowerDegree82Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x))=c} := by

  have he : ((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x))=(boundaryImPowerRow77_15Degree82Norm x).val+(boundaryImPowerRow77_16Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree82Norm x).property (boundaryImPowerRow77_16Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree82Norm,boundaryImPowerRow77_16Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x))))=(boundaryImPowerRow77_14Degree82Norm x).val+(boundaryFullPowerDegree82Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree82Norm x).property (boundaryFullPowerDegree82Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree82Norm,boundaryFullPowerDegree82Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x))))))=(boundaryFullPowerDegree82Block33Norm x).val+(boundaryFullPowerDegree82Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block33Norm x).property (boundaryFullPowerDegree82Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block33Norm,boundaryFullPowerDegree82Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x))=c} := by

  have he : ((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x))=(boundaryImPowerRow77_18Degree82Norm x).val+(boundaryImPowerRow77_19Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree82Norm x).property (boundaryImPowerRow77_19Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree82Norm,boundaryImPowerRow77_19Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x))))=(boundaryImPowerRow77_17Degree82Norm x).val+(boundaryFullPowerDegree82Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree82Norm x).property (boundaryFullPowerDegree82Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree82Norm,boundaryFullPowerDegree82Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))=c} := by

  have he : ((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))=(boundaryImPowerRow77_21Degree82Norm x).val+(boundaryLowPowerRow77Degree82Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree82Norm x).property (boundaryLowPowerRow77Degree82Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree82Norm,boundaryLowPowerRow77Degree82Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))=(boundaryImPowerRow77_20Degree82Norm x).val+(boundaryFullPowerDegree82Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree82Norm x).property (boundaryFullPowerDegree82Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree82Norm,boundaryFullPowerDegree82Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))=(boundaryFullPowerDegree82Block38Norm x).val+(boundaryFullPowerDegree82Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block38Norm x).property (boundaryFullPowerDegree82Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block38Norm,boundaryFullPowerDegree82Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))))=(boundaryFullPowerDegree82Block36Norm x).val+(boundaryFullPowerDegree82Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block36Norm x).property (boundaryFullPowerDegree82Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block36Norm,boundaryFullPowerDegree82Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x)))))))))+(((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x)))))))))+(((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))))))=(boundaryFullPowerDegree82Block31Norm x).val+(boundaryFullPowerDegree82Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block31Norm x).property (boundaryFullPowerDegree82Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block31Norm,boundaryFullPowerDegree82Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree82Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x)))))))))+(((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x)))))))))))+(((((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x)))))))))+(((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x)))))))))+(((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x)))))))))))+(((((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x)))))))))+(((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x))))))))))))=(boundaryFullPowerDegree82Block21Norm x).val+(boundaryFullPowerDegree82Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree82Block21Norm x).property (boundaryFullPowerDegree82Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block21Norm,boundaryFullPowerDegree82Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree82Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 82 x=c} := by

  have he0 : boundaryFullPowerRow77 82 x=((((((((((boundaryRePowerRow77_0 82 x)+(boundaryRePowerRow77_1 82 x)))+(((boundaryRePowerRow77_2 82 x)+(((boundaryRePowerRow77_3 82 x)+(boundaryRePowerRow77_4 82 x)))))))+(((((boundaryRePowerRow77_5 82 x)+(((boundaryRePowerRow77_6 82 x)+(boundaryRePowerRow77_7 82 x)))))+(((boundaryRePowerRow77_8 82 x)+(((boundaryRePowerRow77_9 82 x)+(boundaryRePowerRow77_10 82 x)))))))))+(((((((boundaryRePowerRow77_11 82 x)+(((boundaryRePowerRow77_12 82 x)+(boundaryRePowerRow77_13 82 x)))))+(((boundaryRePowerRow77_14 82 x)+(((boundaryRePowerRow77_15 82 x)+(boundaryRePowerRow77_16 82 x)))))))+(((((boundaryRePowerRow77_17 82 x)+(((boundaryRePowerRow77_18 82 x)+(boundaryRePowerRow77_19 82 x)))))+(((boundaryRePowerRow77_20 82 x)+(((boundaryRePowerRow77_21 82 x)+(boundaryRePowerRow77_22 82 x)))))))))))+(((((((((boundaryImPowerRow77_0 82 x)+(boundaryImPowerRow77_1 82 x)))+(((boundaryImPowerRow77_2 82 x)+(((boundaryImPowerRow77_3 82 x)+(boundaryImPowerRow77_4 82 x)))))))+(((((boundaryImPowerRow77_5 82 x)+(((boundaryImPowerRow77_6 82 x)+(boundaryImPowerRow77_7 82 x)))))+(((boundaryImPowerRow77_8 82 x)+(((boundaryImPowerRow77_9 82 x)+(boundaryImPowerRow77_10 82 x)))))))))+(((((((boundaryImPowerRow77_11 82 x)+(((boundaryImPowerRow77_12 82 x)+(boundaryImPowerRow77_13 82 x)))))+(((boundaryImPowerRow77_14 82 x)+(((boundaryImPowerRow77_15 82 x)+(boundaryImPowerRow77_16 82 x)))))))+(((((boundaryImPowerRow77_17 82 x)+(((boundaryImPowerRow77_18 82 x)+(boundaryImPowerRow77_19 82 x)))))+(((boundaryImPowerRow77_20 82 x)+(((boundaryImPowerRow77_21 82 x)+(boundaryLowPowerRow77 82 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree82Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree82Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
