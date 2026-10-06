import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree89Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree89Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x))=c} := by

  have he : ((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x))=(boundaryRePowerRow77_0Degree89Norm x).val+(boundaryRePowerRow77_1Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree89Norm x).property (boundaryRePowerRow77_1Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree89Norm,boundaryRePowerRow77_1Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x))=c} := by

  have he : ((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x))=(boundaryRePowerRow77_3Degree89Norm x).val+(boundaryRePowerRow77_4Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree89Norm x).property (boundaryRePowerRow77_4Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree89Norm,boundaryRePowerRow77_4Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x))))=(boundaryRePowerRow77_2Degree89Norm x).val+(boundaryFullPowerDegree89Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree89Norm x).property (boundaryFullPowerDegree89Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree89Norm,boundaryFullPowerDegree89Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x))))))=(boundaryFullPowerDegree89Block0Norm x).val+(boundaryFullPowerDegree89Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block0Norm x).property (boundaryFullPowerDegree89Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block0Norm,boundaryFullPowerDegree89Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x))=c} := by

  have he : ((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x))=(boundaryRePowerRow77_6Degree89Norm x).val+(boundaryRePowerRow77_7Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree89Norm x).property (boundaryRePowerRow77_7Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree89Norm,boundaryRePowerRow77_7Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x))))=(boundaryRePowerRow77_5Degree89Norm x).val+(boundaryFullPowerDegree89Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree89Norm x).property (boundaryFullPowerDegree89Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree89Norm,boundaryFullPowerDegree89Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))=c} := by

  have he : ((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))=(boundaryRePowerRow77_9Degree89Norm x).val+(boundaryRePowerRow77_10Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree89Norm x).property (boundaryRePowerRow77_10Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree89Norm,boundaryRePowerRow77_10Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))))=(boundaryRePowerRow77_8Degree89Norm x).val+(boundaryFullPowerDegree89Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree89Norm x).property (boundaryFullPowerDegree89Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree89Norm,boundaryFullPowerDegree89Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))))))=(boundaryFullPowerDegree89Block5Norm x).val+(boundaryFullPowerDegree89Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block5Norm x).property (boundaryFullPowerDegree89Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block5Norm,boundaryFullPowerDegree89Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x))))))))=(boundaryFullPowerDegree89Block3Norm x).val+(boundaryFullPowerDegree89Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block3Norm x).property (boundaryFullPowerDegree89Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block3Norm,boundaryFullPowerDegree89Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x))=c} := by

  have he : ((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x))=(boundaryRePowerRow77_12Degree89Norm x).val+(boundaryRePowerRow77_13Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree89Norm x).property (boundaryRePowerRow77_13Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree89Norm,boundaryRePowerRow77_13Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x))))=(boundaryRePowerRow77_11Degree89Norm x).val+(boundaryFullPowerDegree89Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree89Norm x).property (boundaryFullPowerDegree89Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree89Norm,boundaryFullPowerDegree89Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x))=c} := by

  have he : ((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x))=(boundaryRePowerRow77_15Degree89Norm x).val+(boundaryRePowerRow77_16Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree89Norm x).property (boundaryRePowerRow77_16Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree89Norm,boundaryRePowerRow77_16Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x))))=(boundaryRePowerRow77_14Degree89Norm x).val+(boundaryFullPowerDegree89Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree89Norm x).property (boundaryFullPowerDegree89Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree89Norm,boundaryFullPowerDegree89Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x))))))=(boundaryFullPowerDegree89Block11Norm x).val+(boundaryFullPowerDegree89Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block11Norm x).property (boundaryFullPowerDegree89Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block11Norm,boundaryFullPowerDegree89Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x))=c} := by

  have he : ((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x))=(boundaryRePowerRow77_18Degree89Norm x).val+(boundaryRePowerRow77_19Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree89Norm x).property (boundaryRePowerRow77_19Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree89Norm,boundaryRePowerRow77_19Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x))))=(boundaryRePowerRow77_17Degree89Norm x).val+(boundaryFullPowerDegree89Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree89Norm x).property (boundaryFullPowerDegree89Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree89Norm,boundaryFullPowerDegree89Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))=c} := by

  have he : ((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))=(boundaryRePowerRow77_21Degree89Norm x).val+(boundaryRePowerRow77_22Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree89Norm x).property (boundaryRePowerRow77_22Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree89Norm,boundaryRePowerRow77_22Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))=(boundaryRePowerRow77_20Degree89Norm x).val+(boundaryFullPowerDegree89Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree89Norm x).property (boundaryFullPowerDegree89Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree89Norm,boundaryFullPowerDegree89Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))))=(boundaryFullPowerDegree89Block16Norm x).val+(boundaryFullPowerDegree89Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block16Norm x).property (boundaryFullPowerDegree89Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block16Norm,boundaryFullPowerDegree89Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))))))=(boundaryFullPowerDegree89Block14Norm x).val+(boundaryFullPowerDegree89Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block14Norm x).property (boundaryFullPowerDegree89Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block14Norm,boundaryFullPowerDegree89Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x)))))))))+(((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x)))))))))+(((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x))))))))))=(boundaryFullPowerDegree89Block9Norm x).val+(boundaryFullPowerDegree89Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block9Norm x).property (boundaryFullPowerDegree89Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block9Norm,boundaryFullPowerDegree89Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x))=c} := by

  have he : ((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x))=(boundaryImPowerRow77_0Degree89Norm x).val+(boundaryImPowerRow77_1Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree89Norm x).property (boundaryImPowerRow77_1Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree89Norm,boundaryImPowerRow77_1Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x))=c} := by

  have he : ((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x))=(boundaryImPowerRow77_3Degree89Norm x).val+(boundaryImPowerRow77_4Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree89Norm x).property (boundaryImPowerRow77_4Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree89Norm,boundaryImPowerRow77_4Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x))))=(boundaryImPowerRow77_2Degree89Norm x).val+(boundaryFullPowerDegree89Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree89Norm x).property (boundaryFullPowerDegree89Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree89Norm,boundaryFullPowerDegree89Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x))))))=(boundaryFullPowerDegree89Block22Norm x).val+(boundaryFullPowerDegree89Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block22Norm x).property (boundaryFullPowerDegree89Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block22Norm,boundaryFullPowerDegree89Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x))=c} := by

  have he : ((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x))=(boundaryImPowerRow77_6Degree89Norm x).val+(boundaryImPowerRow77_7Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree89Norm x).property (boundaryImPowerRow77_7Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree89Norm,boundaryImPowerRow77_7Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x))))=(boundaryImPowerRow77_5Degree89Norm x).val+(boundaryFullPowerDegree89Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree89Norm x).property (boundaryFullPowerDegree89Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree89Norm,boundaryFullPowerDegree89Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))=c} := by

  have he : ((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))=(boundaryImPowerRow77_9Degree89Norm x).val+(boundaryImPowerRow77_10Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree89Norm x).property (boundaryImPowerRow77_10Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree89Norm,boundaryImPowerRow77_10Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))))=(boundaryImPowerRow77_8Degree89Norm x).val+(boundaryFullPowerDegree89Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree89Norm x).property (boundaryFullPowerDegree89Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree89Norm,boundaryFullPowerDegree89Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))))))=(boundaryFullPowerDegree89Block27Norm x).val+(boundaryFullPowerDegree89Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block27Norm x).property (boundaryFullPowerDegree89Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block27Norm,boundaryFullPowerDegree89Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x))))))))=(boundaryFullPowerDegree89Block25Norm x).val+(boundaryFullPowerDegree89Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block25Norm x).property (boundaryFullPowerDegree89Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block25Norm,boundaryFullPowerDegree89Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x))=c} := by

  have he : ((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x))=(boundaryImPowerRow77_12Degree89Norm x).val+(boundaryImPowerRow77_13Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree89Norm x).property (boundaryImPowerRow77_13Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree89Norm,boundaryImPowerRow77_13Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x))))=(boundaryImPowerRow77_11Degree89Norm x).val+(boundaryFullPowerDegree89Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree89Norm x).property (boundaryFullPowerDegree89Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree89Norm,boundaryFullPowerDegree89Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x))=c} := by

  have he : ((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x))=(boundaryImPowerRow77_15Degree89Norm x).val+(boundaryImPowerRow77_16Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree89Norm x).property (boundaryImPowerRow77_16Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree89Norm,boundaryImPowerRow77_16Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x))))=(boundaryImPowerRow77_14Degree89Norm x).val+(boundaryFullPowerDegree89Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree89Norm x).property (boundaryFullPowerDegree89Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree89Norm,boundaryFullPowerDegree89Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x))))))=(boundaryFullPowerDegree89Block33Norm x).val+(boundaryFullPowerDegree89Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block33Norm x).property (boundaryFullPowerDegree89Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block33Norm,boundaryFullPowerDegree89Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x))=c} := by

  have he : ((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x))=(boundaryImPowerRow77_18Degree89Norm x).val+(boundaryImPowerRow77_19Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree89Norm x).property (boundaryImPowerRow77_19Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree89Norm,boundaryImPowerRow77_19Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x))))=(boundaryImPowerRow77_17Degree89Norm x).val+(boundaryFullPowerDegree89Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree89Norm x).property (boundaryFullPowerDegree89Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree89Norm,boundaryFullPowerDegree89Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))=c} := by

  have he : ((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))=(boundaryImPowerRow77_21Degree89Norm x).val+(boundaryLowPowerRow77Degree89Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree89Norm x).property (boundaryLowPowerRow77Degree89Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree89Norm,boundaryLowPowerRow77Degree89Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))=(boundaryImPowerRow77_20Degree89Norm x).val+(boundaryFullPowerDegree89Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree89Norm x).property (boundaryFullPowerDegree89Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree89Norm,boundaryFullPowerDegree89Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))=(boundaryFullPowerDegree89Block38Norm x).val+(boundaryFullPowerDegree89Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block38Norm x).property (boundaryFullPowerDegree89Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block38Norm,boundaryFullPowerDegree89Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))))=(boundaryFullPowerDegree89Block36Norm x).val+(boundaryFullPowerDegree89Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block36Norm x).property (boundaryFullPowerDegree89Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block36Norm,boundaryFullPowerDegree89Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x)))))))))+(((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x)))))))))+(((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))))))=(boundaryFullPowerDegree89Block31Norm x).val+(boundaryFullPowerDegree89Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block31Norm x).property (boundaryFullPowerDegree89Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block31Norm,boundaryFullPowerDegree89Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree89Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x)))))))))+(((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x)))))))))))+(((((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x)))))))))+(((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x)))))))))+(((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x)))))))))))+(((((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x)))))))))+(((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x))))))))))))=(boundaryFullPowerDegree89Block21Norm x).val+(boundaryFullPowerDegree89Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree89Block21Norm x).property (boundaryFullPowerDegree89Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block21Norm,boundaryFullPowerDegree89Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree89Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 89 x=c} := by

  have he0 : boundaryFullPowerRow77 89 x=((((((((((boundaryRePowerRow77_0 89 x)+(boundaryRePowerRow77_1 89 x)))+(((boundaryRePowerRow77_2 89 x)+(((boundaryRePowerRow77_3 89 x)+(boundaryRePowerRow77_4 89 x)))))))+(((((boundaryRePowerRow77_5 89 x)+(((boundaryRePowerRow77_6 89 x)+(boundaryRePowerRow77_7 89 x)))))+(((boundaryRePowerRow77_8 89 x)+(((boundaryRePowerRow77_9 89 x)+(boundaryRePowerRow77_10 89 x)))))))))+(((((((boundaryRePowerRow77_11 89 x)+(((boundaryRePowerRow77_12 89 x)+(boundaryRePowerRow77_13 89 x)))))+(((boundaryRePowerRow77_14 89 x)+(((boundaryRePowerRow77_15 89 x)+(boundaryRePowerRow77_16 89 x)))))))+(((((boundaryRePowerRow77_17 89 x)+(((boundaryRePowerRow77_18 89 x)+(boundaryRePowerRow77_19 89 x)))))+(((boundaryRePowerRow77_20 89 x)+(((boundaryRePowerRow77_21 89 x)+(boundaryRePowerRow77_22 89 x)))))))))))+(((((((((boundaryImPowerRow77_0 89 x)+(boundaryImPowerRow77_1 89 x)))+(((boundaryImPowerRow77_2 89 x)+(((boundaryImPowerRow77_3 89 x)+(boundaryImPowerRow77_4 89 x)))))))+(((((boundaryImPowerRow77_5 89 x)+(((boundaryImPowerRow77_6 89 x)+(boundaryImPowerRow77_7 89 x)))))+(((boundaryImPowerRow77_8 89 x)+(((boundaryImPowerRow77_9 89 x)+(boundaryImPowerRow77_10 89 x)))))))))+(((((((boundaryImPowerRow77_11 89 x)+(((boundaryImPowerRow77_12 89 x)+(boundaryImPowerRow77_13 89 x)))))+(((boundaryImPowerRow77_14 89 x)+(((boundaryImPowerRow77_15 89 x)+(boundaryImPowerRow77_16 89 x)))))))+(((((boundaryImPowerRow77_17 89 x)+(((boundaryImPowerRow77_18 89 x)+(boundaryImPowerRow77_19 89 x)))))+(((boundaryImPowerRow77_20 89 x)+(((boundaryImPowerRow77_21 89 x)+(boundaryLowPowerRow77 89 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree89Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree89Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
