import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree23Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree23Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x))=c} := by

  have he : ((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x))=(boundaryRePowerRow77_0Degree23Norm x).val+(boundaryRePowerRow77_1Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree23Norm x).property (boundaryRePowerRow77_1Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree23Norm,boundaryRePowerRow77_1Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x))=c} := by

  have he : ((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x))=(boundaryRePowerRow77_3Degree23Norm x).val+(boundaryRePowerRow77_4Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree23Norm x).property (boundaryRePowerRow77_4Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree23Norm,boundaryRePowerRow77_4Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x))))=(boundaryRePowerRow77_2Degree23Norm x).val+(boundaryFullPowerDegree23Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree23Norm x).property (boundaryFullPowerDegree23Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree23Norm,boundaryFullPowerDegree23Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x))))))=(boundaryFullPowerDegree23Block0Norm x).val+(boundaryFullPowerDegree23Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block0Norm x).property (boundaryFullPowerDegree23Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block0Norm,boundaryFullPowerDegree23Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x))=c} := by

  have he : ((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x))=(boundaryRePowerRow77_6Degree23Norm x).val+(boundaryRePowerRow77_7Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree23Norm x).property (boundaryRePowerRow77_7Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree23Norm,boundaryRePowerRow77_7Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x))))=(boundaryRePowerRow77_5Degree23Norm x).val+(boundaryFullPowerDegree23Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree23Norm x).property (boundaryFullPowerDegree23Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree23Norm,boundaryFullPowerDegree23Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))=c} := by

  have he : ((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))=(boundaryRePowerRow77_9Degree23Norm x).val+(boundaryRePowerRow77_10Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree23Norm x).property (boundaryRePowerRow77_10Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree23Norm,boundaryRePowerRow77_10Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))))=(boundaryRePowerRow77_8Degree23Norm x).val+(boundaryFullPowerDegree23Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree23Norm x).property (boundaryFullPowerDegree23Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree23Norm,boundaryFullPowerDegree23Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))))))=(boundaryFullPowerDegree23Block5Norm x).val+(boundaryFullPowerDegree23Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block5Norm x).property (boundaryFullPowerDegree23Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block5Norm,boundaryFullPowerDegree23Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x))))))))=(boundaryFullPowerDegree23Block3Norm x).val+(boundaryFullPowerDegree23Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block3Norm x).property (boundaryFullPowerDegree23Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block3Norm,boundaryFullPowerDegree23Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x))=c} := by

  have he : ((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x))=(boundaryRePowerRow77_12Degree23Norm x).val+(boundaryRePowerRow77_13Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree23Norm x).property (boundaryRePowerRow77_13Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree23Norm,boundaryRePowerRow77_13Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x))))=(boundaryRePowerRow77_11Degree23Norm x).val+(boundaryFullPowerDegree23Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree23Norm x).property (boundaryFullPowerDegree23Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree23Norm,boundaryFullPowerDegree23Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x))=c} := by

  have he : ((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x))=(boundaryRePowerRow77_15Degree23Norm x).val+(boundaryRePowerRow77_16Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree23Norm x).property (boundaryRePowerRow77_16Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree23Norm,boundaryRePowerRow77_16Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x))))=(boundaryRePowerRow77_14Degree23Norm x).val+(boundaryFullPowerDegree23Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree23Norm x).property (boundaryFullPowerDegree23Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree23Norm,boundaryFullPowerDegree23Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x))))))=(boundaryFullPowerDegree23Block11Norm x).val+(boundaryFullPowerDegree23Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block11Norm x).property (boundaryFullPowerDegree23Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block11Norm,boundaryFullPowerDegree23Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x))=c} := by

  have he : ((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x))=(boundaryRePowerRow77_18Degree23Norm x).val+(boundaryRePowerRow77_19Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree23Norm x).property (boundaryRePowerRow77_19Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree23Norm,boundaryRePowerRow77_19Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x))))=(boundaryRePowerRow77_17Degree23Norm x).val+(boundaryFullPowerDegree23Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree23Norm x).property (boundaryFullPowerDegree23Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree23Norm,boundaryFullPowerDegree23Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))=c} := by

  have he : ((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))=(boundaryRePowerRow77_21Degree23Norm x).val+(boundaryRePowerRow77_22Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree23Norm x).property (boundaryRePowerRow77_22Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree23Norm,boundaryRePowerRow77_22Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))=(boundaryRePowerRow77_20Degree23Norm x).val+(boundaryFullPowerDegree23Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree23Norm x).property (boundaryFullPowerDegree23Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree23Norm,boundaryFullPowerDegree23Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))))=(boundaryFullPowerDegree23Block16Norm x).val+(boundaryFullPowerDegree23Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block16Norm x).property (boundaryFullPowerDegree23Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block16Norm,boundaryFullPowerDegree23Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))))))=(boundaryFullPowerDegree23Block14Norm x).val+(boundaryFullPowerDegree23Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block14Norm x).property (boundaryFullPowerDegree23Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block14Norm,boundaryFullPowerDegree23Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x)))))))))+(((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x)))))))))+(((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x))))))))))=(boundaryFullPowerDegree23Block9Norm x).val+(boundaryFullPowerDegree23Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block9Norm x).property (boundaryFullPowerDegree23Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block9Norm,boundaryFullPowerDegree23Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x))=c} := by

  have he : ((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x))=(boundaryImPowerRow77_0Degree23Norm x).val+(boundaryImPowerRow77_1Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree23Norm x).property (boundaryImPowerRow77_1Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree23Norm,boundaryImPowerRow77_1Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x))=c} := by

  have he : ((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x))=(boundaryImPowerRow77_3Degree23Norm x).val+(boundaryImPowerRow77_4Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree23Norm x).property (boundaryImPowerRow77_4Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree23Norm,boundaryImPowerRow77_4Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x))))=(boundaryImPowerRow77_2Degree23Norm x).val+(boundaryFullPowerDegree23Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree23Norm x).property (boundaryFullPowerDegree23Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree23Norm,boundaryFullPowerDegree23Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x))))))=(boundaryFullPowerDegree23Block22Norm x).val+(boundaryFullPowerDegree23Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block22Norm x).property (boundaryFullPowerDegree23Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block22Norm,boundaryFullPowerDegree23Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x))=c} := by

  have he : ((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x))=(boundaryImPowerRow77_6Degree23Norm x).val+(boundaryImPowerRow77_7Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree23Norm x).property (boundaryImPowerRow77_7Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree23Norm,boundaryImPowerRow77_7Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x))))=(boundaryImPowerRow77_5Degree23Norm x).val+(boundaryFullPowerDegree23Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree23Norm x).property (boundaryFullPowerDegree23Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree23Norm,boundaryFullPowerDegree23Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))=c} := by

  have he : ((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))=(boundaryImPowerRow77_9Degree23Norm x).val+(boundaryImPowerRow77_10Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree23Norm x).property (boundaryImPowerRow77_10Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree23Norm,boundaryImPowerRow77_10Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))))=(boundaryImPowerRow77_8Degree23Norm x).val+(boundaryFullPowerDegree23Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree23Norm x).property (boundaryFullPowerDegree23Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree23Norm,boundaryFullPowerDegree23Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))))))=(boundaryFullPowerDegree23Block27Norm x).val+(boundaryFullPowerDegree23Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block27Norm x).property (boundaryFullPowerDegree23Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block27Norm,boundaryFullPowerDegree23Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x))))))))=(boundaryFullPowerDegree23Block25Norm x).val+(boundaryFullPowerDegree23Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block25Norm x).property (boundaryFullPowerDegree23Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block25Norm,boundaryFullPowerDegree23Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x))=c} := by

  have he : ((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x))=(boundaryImPowerRow77_12Degree23Norm x).val+(boundaryImPowerRow77_13Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree23Norm x).property (boundaryImPowerRow77_13Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree23Norm,boundaryImPowerRow77_13Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x))))=(boundaryImPowerRow77_11Degree23Norm x).val+(boundaryFullPowerDegree23Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree23Norm x).property (boundaryFullPowerDegree23Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree23Norm,boundaryFullPowerDegree23Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x))=c} := by

  have he : ((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x))=(boundaryImPowerRow77_15Degree23Norm x).val+(boundaryImPowerRow77_16Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree23Norm x).property (boundaryImPowerRow77_16Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree23Norm,boundaryImPowerRow77_16Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x))))=(boundaryImPowerRow77_14Degree23Norm x).val+(boundaryFullPowerDegree23Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree23Norm x).property (boundaryFullPowerDegree23Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree23Norm,boundaryFullPowerDegree23Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x))))))=(boundaryFullPowerDegree23Block33Norm x).val+(boundaryFullPowerDegree23Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block33Norm x).property (boundaryFullPowerDegree23Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block33Norm,boundaryFullPowerDegree23Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x))=c} := by

  have he : ((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x))=(boundaryImPowerRow77_18Degree23Norm x).val+(boundaryImPowerRow77_19Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree23Norm x).property (boundaryImPowerRow77_19Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree23Norm,boundaryImPowerRow77_19Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x))))=(boundaryImPowerRow77_17Degree23Norm x).val+(boundaryFullPowerDegree23Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree23Norm x).property (boundaryFullPowerDegree23Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree23Norm,boundaryFullPowerDegree23Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))=c} := by

  have he : ((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))=(boundaryImPowerRow77_21Degree23Norm x).val+(boundaryLowPowerRow77Degree23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree23Norm x).property (boundaryLowPowerRow77Degree23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree23Norm,boundaryLowPowerRow77Degree23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))=(boundaryImPowerRow77_20Degree23Norm x).val+(boundaryFullPowerDegree23Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree23Norm x).property (boundaryFullPowerDegree23Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree23Norm,boundaryFullPowerDegree23Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))=(boundaryFullPowerDegree23Block38Norm x).val+(boundaryFullPowerDegree23Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block38Norm x).property (boundaryFullPowerDegree23Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block38Norm,boundaryFullPowerDegree23Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))))=(boundaryFullPowerDegree23Block36Norm x).val+(boundaryFullPowerDegree23Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block36Norm x).property (boundaryFullPowerDegree23Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block36Norm,boundaryFullPowerDegree23Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x)))))))))+(((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x)))))))))+(((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))))))=(boundaryFullPowerDegree23Block31Norm x).val+(boundaryFullPowerDegree23Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block31Norm x).property (boundaryFullPowerDegree23Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block31Norm,boundaryFullPowerDegree23Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree23Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x)))))))))+(((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x)))))))))))+(((((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x)))))))))+(((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x)))))))))+(((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x)))))))))))+(((((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x)))))))))+(((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x))))))))))))=(boundaryFullPowerDegree23Block21Norm x).val+(boundaryFullPowerDegree23Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree23Block21Norm x).property (boundaryFullPowerDegree23Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block21Norm,boundaryFullPowerDegree23Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree23Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 23 x=c} := by

  have he0 : boundaryFullPowerRow77 23 x=((((((((((boundaryRePowerRow77_0 23 x)+(boundaryRePowerRow77_1 23 x)))+(((boundaryRePowerRow77_2 23 x)+(((boundaryRePowerRow77_3 23 x)+(boundaryRePowerRow77_4 23 x)))))))+(((((boundaryRePowerRow77_5 23 x)+(((boundaryRePowerRow77_6 23 x)+(boundaryRePowerRow77_7 23 x)))))+(((boundaryRePowerRow77_8 23 x)+(((boundaryRePowerRow77_9 23 x)+(boundaryRePowerRow77_10 23 x)))))))))+(((((((boundaryRePowerRow77_11 23 x)+(((boundaryRePowerRow77_12 23 x)+(boundaryRePowerRow77_13 23 x)))))+(((boundaryRePowerRow77_14 23 x)+(((boundaryRePowerRow77_15 23 x)+(boundaryRePowerRow77_16 23 x)))))))+(((((boundaryRePowerRow77_17 23 x)+(((boundaryRePowerRow77_18 23 x)+(boundaryRePowerRow77_19 23 x)))))+(((boundaryRePowerRow77_20 23 x)+(((boundaryRePowerRow77_21 23 x)+(boundaryRePowerRow77_22 23 x)))))))))))+(((((((((boundaryImPowerRow77_0 23 x)+(boundaryImPowerRow77_1 23 x)))+(((boundaryImPowerRow77_2 23 x)+(((boundaryImPowerRow77_3 23 x)+(boundaryImPowerRow77_4 23 x)))))))+(((((boundaryImPowerRow77_5 23 x)+(((boundaryImPowerRow77_6 23 x)+(boundaryImPowerRow77_7 23 x)))))+(((boundaryImPowerRow77_8 23 x)+(((boundaryImPowerRow77_9 23 x)+(boundaryImPowerRow77_10 23 x)))))))))+(((((((boundaryImPowerRow77_11 23 x)+(((boundaryImPowerRow77_12 23 x)+(boundaryImPowerRow77_13 23 x)))))+(((boundaryImPowerRow77_14 23 x)+(((boundaryImPowerRow77_15 23 x)+(boundaryImPowerRow77_16 23 x)))))))+(((((boundaryImPowerRow77_17 23 x)+(((boundaryImPowerRow77_18 23 x)+(boundaryImPowerRow77_19 23 x)))))+(((boundaryImPowerRow77_20 23 x)+(((boundaryImPowerRow77_21 23 x)+(boundaryLowPowerRow77 23 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree23Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree23Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
