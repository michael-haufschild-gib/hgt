import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree4Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree4Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x))=c} := by

  have he : ((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x))=(boundaryRePowerRow77_0Degree4Norm x).val+(boundaryRePowerRow77_1Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree4Norm x).property (boundaryRePowerRow77_1Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree4Norm,boundaryRePowerRow77_1Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x))=c} := by

  have he : ((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x))=(boundaryRePowerRow77_3Degree4Norm x).val+(boundaryRePowerRow77_4Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree4Norm x).property (boundaryRePowerRow77_4Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree4Norm,boundaryRePowerRow77_4Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x))))=(boundaryRePowerRow77_2Degree4Norm x).val+(boundaryFullPowerDegree4Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree4Norm x).property (boundaryFullPowerDegree4Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree4Norm,boundaryFullPowerDegree4Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x))))))=(boundaryFullPowerDegree4Block0Norm x).val+(boundaryFullPowerDegree4Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block0Norm x).property (boundaryFullPowerDegree4Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block0Norm,boundaryFullPowerDegree4Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x))=c} := by

  have he : ((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x))=(boundaryRePowerRow77_6Degree4Norm x).val+(boundaryRePowerRow77_7Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree4Norm x).property (boundaryRePowerRow77_7Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree4Norm,boundaryRePowerRow77_7Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x))))=(boundaryRePowerRow77_5Degree4Norm x).val+(boundaryFullPowerDegree4Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree4Norm x).property (boundaryFullPowerDegree4Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree4Norm,boundaryFullPowerDegree4Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))=c} := by

  have he : ((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))=(boundaryRePowerRow77_9Degree4Norm x).val+(boundaryRePowerRow77_10Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree4Norm x).property (boundaryRePowerRow77_10Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree4Norm,boundaryRePowerRow77_10Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))))=(boundaryRePowerRow77_8Degree4Norm x).val+(boundaryFullPowerDegree4Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree4Norm x).property (boundaryFullPowerDegree4Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree4Norm,boundaryFullPowerDegree4Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))))))=(boundaryFullPowerDegree4Block5Norm x).val+(boundaryFullPowerDegree4Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block5Norm x).property (boundaryFullPowerDegree4Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block5Norm,boundaryFullPowerDegree4Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x))))))))=(boundaryFullPowerDegree4Block3Norm x).val+(boundaryFullPowerDegree4Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block3Norm x).property (boundaryFullPowerDegree4Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block3Norm,boundaryFullPowerDegree4Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x))=c} := by

  have he : ((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x))=(boundaryRePowerRow77_12Degree4Norm x).val+(boundaryRePowerRow77_13Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree4Norm x).property (boundaryRePowerRow77_13Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree4Norm,boundaryRePowerRow77_13Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x))))=(boundaryRePowerRow77_11Degree4Norm x).val+(boundaryFullPowerDegree4Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree4Norm x).property (boundaryFullPowerDegree4Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree4Norm,boundaryFullPowerDegree4Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x))=c} := by

  have he : ((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x))=(boundaryRePowerRow77_15Degree4Norm x).val+(boundaryRePowerRow77_16Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree4Norm x).property (boundaryRePowerRow77_16Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree4Norm,boundaryRePowerRow77_16Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x))))=(boundaryRePowerRow77_14Degree4Norm x).val+(boundaryFullPowerDegree4Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree4Norm x).property (boundaryFullPowerDegree4Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree4Norm,boundaryFullPowerDegree4Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x))))))=(boundaryFullPowerDegree4Block11Norm x).val+(boundaryFullPowerDegree4Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block11Norm x).property (boundaryFullPowerDegree4Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block11Norm,boundaryFullPowerDegree4Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x))=c} := by

  have he : ((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x))=(boundaryRePowerRow77_18Degree4Norm x).val+(boundaryRePowerRow77_19Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree4Norm x).property (boundaryRePowerRow77_19Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree4Norm,boundaryRePowerRow77_19Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x))))=(boundaryRePowerRow77_17Degree4Norm x).val+(boundaryFullPowerDegree4Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree4Norm x).property (boundaryFullPowerDegree4Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree4Norm,boundaryFullPowerDegree4Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))=c} := by

  have he : ((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))=(boundaryRePowerRow77_21Degree4Norm x).val+(boundaryRePowerRow77_22Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree4Norm x).property (boundaryRePowerRow77_22Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree4Norm,boundaryRePowerRow77_22Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))=(boundaryRePowerRow77_20Degree4Norm x).val+(boundaryFullPowerDegree4Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree4Norm x).property (boundaryFullPowerDegree4Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree4Norm,boundaryFullPowerDegree4Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))))=(boundaryFullPowerDegree4Block16Norm x).val+(boundaryFullPowerDegree4Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block16Norm x).property (boundaryFullPowerDegree4Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block16Norm,boundaryFullPowerDegree4Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))))))=(boundaryFullPowerDegree4Block14Norm x).val+(boundaryFullPowerDegree4Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block14Norm x).property (boundaryFullPowerDegree4Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block14Norm,boundaryFullPowerDegree4Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x)))))))))+(((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x)))))))))+(((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x))))))))))=(boundaryFullPowerDegree4Block9Norm x).val+(boundaryFullPowerDegree4Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block9Norm x).property (boundaryFullPowerDegree4Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block9Norm,boundaryFullPowerDegree4Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x))=c} := by

  have he : ((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x))=(boundaryImPowerRow77_0Degree4Norm x).val+(boundaryImPowerRow77_1Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree4Norm x).property (boundaryImPowerRow77_1Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree4Norm,boundaryImPowerRow77_1Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x))=c} := by

  have he : ((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x))=(boundaryImPowerRow77_3Degree4Norm x).val+(boundaryImPowerRow77_4Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree4Norm x).property (boundaryImPowerRow77_4Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree4Norm,boundaryImPowerRow77_4Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x))))=(boundaryImPowerRow77_2Degree4Norm x).val+(boundaryFullPowerDegree4Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree4Norm x).property (boundaryFullPowerDegree4Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree4Norm,boundaryFullPowerDegree4Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x))))))=(boundaryFullPowerDegree4Block22Norm x).val+(boundaryFullPowerDegree4Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block22Norm x).property (boundaryFullPowerDegree4Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block22Norm,boundaryFullPowerDegree4Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x))=c} := by

  have he : ((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x))=(boundaryImPowerRow77_6Degree4Norm x).val+(boundaryImPowerRow77_7Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree4Norm x).property (boundaryImPowerRow77_7Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree4Norm,boundaryImPowerRow77_7Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x))))=(boundaryImPowerRow77_5Degree4Norm x).val+(boundaryFullPowerDegree4Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree4Norm x).property (boundaryFullPowerDegree4Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree4Norm,boundaryFullPowerDegree4Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))=c} := by

  have he : ((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))=(boundaryImPowerRow77_9Degree4Norm x).val+(boundaryImPowerRow77_10Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree4Norm x).property (boundaryImPowerRow77_10Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree4Norm,boundaryImPowerRow77_10Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))))=(boundaryImPowerRow77_8Degree4Norm x).val+(boundaryFullPowerDegree4Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree4Norm x).property (boundaryFullPowerDegree4Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree4Norm,boundaryFullPowerDegree4Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))))))=(boundaryFullPowerDegree4Block27Norm x).val+(boundaryFullPowerDegree4Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block27Norm x).property (boundaryFullPowerDegree4Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block27Norm,boundaryFullPowerDegree4Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x))))))))=(boundaryFullPowerDegree4Block25Norm x).val+(boundaryFullPowerDegree4Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block25Norm x).property (boundaryFullPowerDegree4Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block25Norm,boundaryFullPowerDegree4Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x))=c} := by

  have he : ((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x))=(boundaryImPowerRow77_12Degree4Norm x).val+(boundaryImPowerRow77_13Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree4Norm x).property (boundaryImPowerRow77_13Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree4Norm,boundaryImPowerRow77_13Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x))))=(boundaryImPowerRow77_11Degree4Norm x).val+(boundaryFullPowerDegree4Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree4Norm x).property (boundaryFullPowerDegree4Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree4Norm,boundaryFullPowerDegree4Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x))=c} := by

  have he : ((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x))=(boundaryImPowerRow77_15Degree4Norm x).val+(boundaryImPowerRow77_16Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree4Norm x).property (boundaryImPowerRow77_16Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree4Norm,boundaryImPowerRow77_16Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x))))=(boundaryImPowerRow77_14Degree4Norm x).val+(boundaryFullPowerDegree4Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree4Norm x).property (boundaryFullPowerDegree4Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree4Norm,boundaryFullPowerDegree4Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x))))))=(boundaryFullPowerDegree4Block33Norm x).val+(boundaryFullPowerDegree4Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block33Norm x).property (boundaryFullPowerDegree4Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block33Norm,boundaryFullPowerDegree4Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x))=c} := by

  have he : ((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x))=(boundaryImPowerRow77_18Degree4Norm x).val+(boundaryImPowerRow77_19Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree4Norm x).property (boundaryImPowerRow77_19Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree4Norm,boundaryImPowerRow77_19Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x))))=(boundaryImPowerRow77_17Degree4Norm x).val+(boundaryFullPowerDegree4Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree4Norm x).property (boundaryFullPowerDegree4Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree4Norm,boundaryFullPowerDegree4Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))=c} := by

  have he : ((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))=(boundaryImPowerRow77_21Degree4Norm x).val+(boundaryLowPowerRow77Degree4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree4Norm x).property (boundaryLowPowerRow77Degree4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree4Norm,boundaryLowPowerRow77Degree4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))=(boundaryImPowerRow77_20Degree4Norm x).val+(boundaryFullPowerDegree4Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree4Norm x).property (boundaryFullPowerDegree4Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree4Norm,boundaryFullPowerDegree4Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))=(boundaryFullPowerDegree4Block38Norm x).val+(boundaryFullPowerDegree4Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block38Norm x).property (boundaryFullPowerDegree4Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block38Norm,boundaryFullPowerDegree4Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))))=(boundaryFullPowerDegree4Block36Norm x).val+(boundaryFullPowerDegree4Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block36Norm x).property (boundaryFullPowerDegree4Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block36Norm,boundaryFullPowerDegree4Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x)))))))))+(((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x)))))))))+(((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))))))=(boundaryFullPowerDegree4Block31Norm x).val+(boundaryFullPowerDegree4Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block31Norm x).property (boundaryFullPowerDegree4Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block31Norm,boundaryFullPowerDegree4Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree4Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x)))))))))+(((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x)))))))))))+(((((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x)))))))))+(((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x)))))))))+(((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x)))))))))))+(((((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x)))))))))+(((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x))))))))))))=(boundaryFullPowerDegree4Block21Norm x).val+(boundaryFullPowerDegree4Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree4Block21Norm x).property (boundaryFullPowerDegree4Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block21Norm,boundaryFullPowerDegree4Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree4Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 4 x=c} := by

  have he0 : boundaryFullPowerRow77 4 x=((((((((((boundaryRePowerRow77_0 4 x)+(boundaryRePowerRow77_1 4 x)))+(((boundaryRePowerRow77_2 4 x)+(((boundaryRePowerRow77_3 4 x)+(boundaryRePowerRow77_4 4 x)))))))+(((((boundaryRePowerRow77_5 4 x)+(((boundaryRePowerRow77_6 4 x)+(boundaryRePowerRow77_7 4 x)))))+(((boundaryRePowerRow77_8 4 x)+(((boundaryRePowerRow77_9 4 x)+(boundaryRePowerRow77_10 4 x)))))))))+(((((((boundaryRePowerRow77_11 4 x)+(((boundaryRePowerRow77_12 4 x)+(boundaryRePowerRow77_13 4 x)))))+(((boundaryRePowerRow77_14 4 x)+(((boundaryRePowerRow77_15 4 x)+(boundaryRePowerRow77_16 4 x)))))))+(((((boundaryRePowerRow77_17 4 x)+(((boundaryRePowerRow77_18 4 x)+(boundaryRePowerRow77_19 4 x)))))+(((boundaryRePowerRow77_20 4 x)+(((boundaryRePowerRow77_21 4 x)+(boundaryRePowerRow77_22 4 x)))))))))))+(((((((((boundaryImPowerRow77_0 4 x)+(boundaryImPowerRow77_1 4 x)))+(((boundaryImPowerRow77_2 4 x)+(((boundaryImPowerRow77_3 4 x)+(boundaryImPowerRow77_4 4 x)))))))+(((((boundaryImPowerRow77_5 4 x)+(((boundaryImPowerRow77_6 4 x)+(boundaryImPowerRow77_7 4 x)))))+(((boundaryImPowerRow77_8 4 x)+(((boundaryImPowerRow77_9 4 x)+(boundaryImPowerRow77_10 4 x)))))))))+(((((((boundaryImPowerRow77_11 4 x)+(((boundaryImPowerRow77_12 4 x)+(boundaryImPowerRow77_13 4 x)))))+(((boundaryImPowerRow77_14 4 x)+(((boundaryImPowerRow77_15 4 x)+(boundaryImPowerRow77_16 4 x)))))))+(((((boundaryImPowerRow77_17 4 x)+(((boundaryImPowerRow77_18 4 x)+(boundaryImPowerRow77_19 4 x)))))+(((boundaryImPowerRow77_20 4 x)+(((boundaryImPowerRow77_21 4 x)+(boundaryLowPowerRow77 4 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree4Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree4Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
