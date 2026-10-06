import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree28Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree28Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x))=c} := by

  have he : ((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x))=(boundaryRePowerRow77_0Degree28Norm x).val+(boundaryRePowerRow77_1Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree28Norm x).property (boundaryRePowerRow77_1Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree28Norm,boundaryRePowerRow77_1Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x))=c} := by

  have he : ((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x))=(boundaryRePowerRow77_3Degree28Norm x).val+(boundaryRePowerRow77_4Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree28Norm x).property (boundaryRePowerRow77_4Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree28Norm,boundaryRePowerRow77_4Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x))))=(boundaryRePowerRow77_2Degree28Norm x).val+(boundaryFullPowerDegree28Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree28Norm x).property (boundaryFullPowerDegree28Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree28Norm,boundaryFullPowerDegree28Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x))))))=(boundaryFullPowerDegree28Block0Norm x).val+(boundaryFullPowerDegree28Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block0Norm x).property (boundaryFullPowerDegree28Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block0Norm,boundaryFullPowerDegree28Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x))=c} := by

  have he : ((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x))=(boundaryRePowerRow77_6Degree28Norm x).val+(boundaryRePowerRow77_7Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree28Norm x).property (boundaryRePowerRow77_7Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree28Norm,boundaryRePowerRow77_7Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x))))=(boundaryRePowerRow77_5Degree28Norm x).val+(boundaryFullPowerDegree28Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree28Norm x).property (boundaryFullPowerDegree28Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree28Norm,boundaryFullPowerDegree28Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))=c} := by

  have he : ((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))=(boundaryRePowerRow77_9Degree28Norm x).val+(boundaryRePowerRow77_10Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree28Norm x).property (boundaryRePowerRow77_10Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree28Norm,boundaryRePowerRow77_10Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))))=(boundaryRePowerRow77_8Degree28Norm x).val+(boundaryFullPowerDegree28Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree28Norm x).property (boundaryFullPowerDegree28Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree28Norm,boundaryFullPowerDegree28Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))))))=(boundaryFullPowerDegree28Block5Norm x).val+(boundaryFullPowerDegree28Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block5Norm x).property (boundaryFullPowerDegree28Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block5Norm,boundaryFullPowerDegree28Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x))))))))=(boundaryFullPowerDegree28Block3Norm x).val+(boundaryFullPowerDegree28Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block3Norm x).property (boundaryFullPowerDegree28Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block3Norm,boundaryFullPowerDegree28Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x))=c} := by

  have he : ((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x))=(boundaryRePowerRow77_12Degree28Norm x).val+(boundaryRePowerRow77_13Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree28Norm x).property (boundaryRePowerRow77_13Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree28Norm,boundaryRePowerRow77_13Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x))))=(boundaryRePowerRow77_11Degree28Norm x).val+(boundaryFullPowerDegree28Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree28Norm x).property (boundaryFullPowerDegree28Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree28Norm,boundaryFullPowerDegree28Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x))=c} := by

  have he : ((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x))=(boundaryRePowerRow77_15Degree28Norm x).val+(boundaryRePowerRow77_16Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree28Norm x).property (boundaryRePowerRow77_16Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree28Norm,boundaryRePowerRow77_16Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x))))=(boundaryRePowerRow77_14Degree28Norm x).val+(boundaryFullPowerDegree28Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree28Norm x).property (boundaryFullPowerDegree28Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree28Norm,boundaryFullPowerDegree28Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x))))))=(boundaryFullPowerDegree28Block11Norm x).val+(boundaryFullPowerDegree28Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block11Norm x).property (boundaryFullPowerDegree28Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block11Norm,boundaryFullPowerDegree28Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x))=c} := by

  have he : ((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x))=(boundaryRePowerRow77_18Degree28Norm x).val+(boundaryRePowerRow77_19Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree28Norm x).property (boundaryRePowerRow77_19Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree28Norm,boundaryRePowerRow77_19Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x))))=(boundaryRePowerRow77_17Degree28Norm x).val+(boundaryFullPowerDegree28Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree28Norm x).property (boundaryFullPowerDegree28Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree28Norm,boundaryFullPowerDegree28Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))=c} := by

  have he : ((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))=(boundaryRePowerRow77_21Degree28Norm x).val+(boundaryRePowerRow77_22Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree28Norm x).property (boundaryRePowerRow77_22Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree28Norm,boundaryRePowerRow77_22Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))=(boundaryRePowerRow77_20Degree28Norm x).val+(boundaryFullPowerDegree28Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree28Norm x).property (boundaryFullPowerDegree28Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree28Norm,boundaryFullPowerDegree28Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))))=(boundaryFullPowerDegree28Block16Norm x).val+(boundaryFullPowerDegree28Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block16Norm x).property (boundaryFullPowerDegree28Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block16Norm,boundaryFullPowerDegree28Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))))))=(boundaryFullPowerDegree28Block14Norm x).val+(boundaryFullPowerDegree28Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block14Norm x).property (boundaryFullPowerDegree28Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block14Norm,boundaryFullPowerDegree28Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x)))))))))+(((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x)))))))))+(((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x))))))))))=(boundaryFullPowerDegree28Block9Norm x).val+(boundaryFullPowerDegree28Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block9Norm x).property (boundaryFullPowerDegree28Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block9Norm,boundaryFullPowerDegree28Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x))=c} := by

  have he : ((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x))=(boundaryImPowerRow77_0Degree28Norm x).val+(boundaryImPowerRow77_1Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree28Norm x).property (boundaryImPowerRow77_1Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree28Norm,boundaryImPowerRow77_1Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x))=c} := by

  have he : ((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x))=(boundaryImPowerRow77_3Degree28Norm x).val+(boundaryImPowerRow77_4Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree28Norm x).property (boundaryImPowerRow77_4Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree28Norm,boundaryImPowerRow77_4Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x))))=(boundaryImPowerRow77_2Degree28Norm x).val+(boundaryFullPowerDegree28Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree28Norm x).property (boundaryFullPowerDegree28Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree28Norm,boundaryFullPowerDegree28Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x))))))=(boundaryFullPowerDegree28Block22Norm x).val+(boundaryFullPowerDegree28Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block22Norm x).property (boundaryFullPowerDegree28Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block22Norm,boundaryFullPowerDegree28Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x))=c} := by

  have he : ((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x))=(boundaryImPowerRow77_6Degree28Norm x).val+(boundaryImPowerRow77_7Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree28Norm x).property (boundaryImPowerRow77_7Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree28Norm,boundaryImPowerRow77_7Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x))))=(boundaryImPowerRow77_5Degree28Norm x).val+(boundaryFullPowerDegree28Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree28Norm x).property (boundaryFullPowerDegree28Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree28Norm,boundaryFullPowerDegree28Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))=c} := by

  have he : ((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))=(boundaryImPowerRow77_9Degree28Norm x).val+(boundaryImPowerRow77_10Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree28Norm x).property (boundaryImPowerRow77_10Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree28Norm,boundaryImPowerRow77_10Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))))=(boundaryImPowerRow77_8Degree28Norm x).val+(boundaryFullPowerDegree28Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree28Norm x).property (boundaryFullPowerDegree28Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree28Norm,boundaryFullPowerDegree28Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))))))=(boundaryFullPowerDegree28Block27Norm x).val+(boundaryFullPowerDegree28Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block27Norm x).property (boundaryFullPowerDegree28Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block27Norm,boundaryFullPowerDegree28Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x))))))))=(boundaryFullPowerDegree28Block25Norm x).val+(boundaryFullPowerDegree28Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block25Norm x).property (boundaryFullPowerDegree28Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block25Norm,boundaryFullPowerDegree28Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x))=c} := by

  have he : ((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x))=(boundaryImPowerRow77_12Degree28Norm x).val+(boundaryImPowerRow77_13Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree28Norm x).property (boundaryImPowerRow77_13Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree28Norm,boundaryImPowerRow77_13Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x))))=(boundaryImPowerRow77_11Degree28Norm x).val+(boundaryFullPowerDegree28Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree28Norm x).property (boundaryFullPowerDegree28Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree28Norm,boundaryFullPowerDegree28Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x))=c} := by

  have he : ((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x))=(boundaryImPowerRow77_15Degree28Norm x).val+(boundaryImPowerRow77_16Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree28Norm x).property (boundaryImPowerRow77_16Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree28Norm,boundaryImPowerRow77_16Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x))))=(boundaryImPowerRow77_14Degree28Norm x).val+(boundaryFullPowerDegree28Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree28Norm x).property (boundaryFullPowerDegree28Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree28Norm,boundaryFullPowerDegree28Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x))))))=(boundaryFullPowerDegree28Block33Norm x).val+(boundaryFullPowerDegree28Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block33Norm x).property (boundaryFullPowerDegree28Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block33Norm,boundaryFullPowerDegree28Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x))=c} := by

  have he : ((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x))=(boundaryImPowerRow77_18Degree28Norm x).val+(boundaryImPowerRow77_19Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree28Norm x).property (boundaryImPowerRow77_19Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree28Norm,boundaryImPowerRow77_19Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x))))=(boundaryImPowerRow77_17Degree28Norm x).val+(boundaryFullPowerDegree28Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree28Norm x).property (boundaryFullPowerDegree28Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree28Norm,boundaryFullPowerDegree28Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))=c} := by

  have he : ((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))=(boundaryImPowerRow77_21Degree28Norm x).val+(boundaryLowPowerRow77Degree28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree28Norm x).property (boundaryLowPowerRow77Degree28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree28Norm,boundaryLowPowerRow77Degree28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))=(boundaryImPowerRow77_20Degree28Norm x).val+(boundaryFullPowerDegree28Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree28Norm x).property (boundaryFullPowerDegree28Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree28Norm,boundaryFullPowerDegree28Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))=(boundaryFullPowerDegree28Block38Norm x).val+(boundaryFullPowerDegree28Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block38Norm x).property (boundaryFullPowerDegree28Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block38Norm,boundaryFullPowerDegree28Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))))=(boundaryFullPowerDegree28Block36Norm x).val+(boundaryFullPowerDegree28Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block36Norm x).property (boundaryFullPowerDegree28Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block36Norm,boundaryFullPowerDegree28Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x)))))))))+(((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x)))))))))+(((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))))))=(boundaryFullPowerDegree28Block31Norm x).val+(boundaryFullPowerDegree28Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block31Norm x).property (boundaryFullPowerDegree28Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block31Norm,boundaryFullPowerDegree28Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree28Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x)))))))))+(((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x)))))))))))+(((((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x)))))))))+(((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x)))))))))+(((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x)))))))))))+(((((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x)))))))))+(((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x))))))))))))=(boundaryFullPowerDegree28Block21Norm x).val+(boundaryFullPowerDegree28Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree28Block21Norm x).property (boundaryFullPowerDegree28Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block21Norm,boundaryFullPowerDegree28Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree28Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 28 x=c} := by

  have he0 : boundaryFullPowerRow77 28 x=((((((((((boundaryRePowerRow77_0 28 x)+(boundaryRePowerRow77_1 28 x)))+(((boundaryRePowerRow77_2 28 x)+(((boundaryRePowerRow77_3 28 x)+(boundaryRePowerRow77_4 28 x)))))))+(((((boundaryRePowerRow77_5 28 x)+(((boundaryRePowerRow77_6 28 x)+(boundaryRePowerRow77_7 28 x)))))+(((boundaryRePowerRow77_8 28 x)+(((boundaryRePowerRow77_9 28 x)+(boundaryRePowerRow77_10 28 x)))))))))+(((((((boundaryRePowerRow77_11 28 x)+(((boundaryRePowerRow77_12 28 x)+(boundaryRePowerRow77_13 28 x)))))+(((boundaryRePowerRow77_14 28 x)+(((boundaryRePowerRow77_15 28 x)+(boundaryRePowerRow77_16 28 x)))))))+(((((boundaryRePowerRow77_17 28 x)+(((boundaryRePowerRow77_18 28 x)+(boundaryRePowerRow77_19 28 x)))))+(((boundaryRePowerRow77_20 28 x)+(((boundaryRePowerRow77_21 28 x)+(boundaryRePowerRow77_22 28 x)))))))))))+(((((((((boundaryImPowerRow77_0 28 x)+(boundaryImPowerRow77_1 28 x)))+(((boundaryImPowerRow77_2 28 x)+(((boundaryImPowerRow77_3 28 x)+(boundaryImPowerRow77_4 28 x)))))))+(((((boundaryImPowerRow77_5 28 x)+(((boundaryImPowerRow77_6 28 x)+(boundaryImPowerRow77_7 28 x)))))+(((boundaryImPowerRow77_8 28 x)+(((boundaryImPowerRow77_9 28 x)+(boundaryImPowerRow77_10 28 x)))))))))+(((((((boundaryImPowerRow77_11 28 x)+(((boundaryImPowerRow77_12 28 x)+(boundaryImPowerRow77_13 28 x)))))+(((boundaryImPowerRow77_14 28 x)+(((boundaryImPowerRow77_15 28 x)+(boundaryImPowerRow77_16 28 x)))))))+(((((boundaryImPowerRow77_17 28 x)+(((boundaryImPowerRow77_18 28 x)+(boundaryImPowerRow77_19 28 x)))))+(((boundaryImPowerRow77_20 28 x)+(((boundaryImPowerRow77_21 28 x)+(boundaryLowPowerRow77 28 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree28Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree28Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
