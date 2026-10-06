import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree73Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree73Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x))=c} := by

  have he : ((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x))=(boundaryRePowerRow77_0Degree73Norm x).val+(boundaryRePowerRow77_1Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree73Norm x).property (boundaryRePowerRow77_1Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree73Norm,boundaryRePowerRow77_1Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x))=c} := by

  have he : ((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x))=(boundaryRePowerRow77_3Degree73Norm x).val+(boundaryRePowerRow77_4Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree73Norm x).property (boundaryRePowerRow77_4Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree73Norm,boundaryRePowerRow77_4Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x))))=(boundaryRePowerRow77_2Degree73Norm x).val+(boundaryFullPowerDegree73Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree73Norm x).property (boundaryFullPowerDegree73Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree73Norm,boundaryFullPowerDegree73Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x))))))=(boundaryFullPowerDegree73Block0Norm x).val+(boundaryFullPowerDegree73Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block0Norm x).property (boundaryFullPowerDegree73Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block0Norm,boundaryFullPowerDegree73Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x))=c} := by

  have he : ((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x))=(boundaryRePowerRow77_6Degree73Norm x).val+(boundaryRePowerRow77_7Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree73Norm x).property (boundaryRePowerRow77_7Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree73Norm,boundaryRePowerRow77_7Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x))))=(boundaryRePowerRow77_5Degree73Norm x).val+(boundaryFullPowerDegree73Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree73Norm x).property (boundaryFullPowerDegree73Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree73Norm,boundaryFullPowerDegree73Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))=c} := by

  have he : ((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))=(boundaryRePowerRow77_9Degree73Norm x).val+(boundaryRePowerRow77_10Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree73Norm x).property (boundaryRePowerRow77_10Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree73Norm,boundaryRePowerRow77_10Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))))=(boundaryRePowerRow77_8Degree73Norm x).val+(boundaryFullPowerDegree73Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree73Norm x).property (boundaryFullPowerDegree73Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree73Norm,boundaryFullPowerDegree73Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))))))=(boundaryFullPowerDegree73Block5Norm x).val+(boundaryFullPowerDegree73Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block5Norm x).property (boundaryFullPowerDegree73Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block5Norm,boundaryFullPowerDegree73Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x))))))))=(boundaryFullPowerDegree73Block3Norm x).val+(boundaryFullPowerDegree73Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block3Norm x).property (boundaryFullPowerDegree73Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block3Norm,boundaryFullPowerDegree73Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x))=c} := by

  have he : ((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x))=(boundaryRePowerRow77_12Degree73Norm x).val+(boundaryRePowerRow77_13Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree73Norm x).property (boundaryRePowerRow77_13Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree73Norm,boundaryRePowerRow77_13Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x))))=(boundaryRePowerRow77_11Degree73Norm x).val+(boundaryFullPowerDegree73Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree73Norm x).property (boundaryFullPowerDegree73Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree73Norm,boundaryFullPowerDegree73Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x))=c} := by

  have he : ((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x))=(boundaryRePowerRow77_15Degree73Norm x).val+(boundaryRePowerRow77_16Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree73Norm x).property (boundaryRePowerRow77_16Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree73Norm,boundaryRePowerRow77_16Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x))))=(boundaryRePowerRow77_14Degree73Norm x).val+(boundaryFullPowerDegree73Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree73Norm x).property (boundaryFullPowerDegree73Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree73Norm,boundaryFullPowerDegree73Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x))))))=(boundaryFullPowerDegree73Block11Norm x).val+(boundaryFullPowerDegree73Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block11Norm x).property (boundaryFullPowerDegree73Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block11Norm,boundaryFullPowerDegree73Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x))=c} := by

  have he : ((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x))=(boundaryRePowerRow77_18Degree73Norm x).val+(boundaryRePowerRow77_19Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree73Norm x).property (boundaryRePowerRow77_19Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree73Norm,boundaryRePowerRow77_19Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x))))=(boundaryRePowerRow77_17Degree73Norm x).val+(boundaryFullPowerDegree73Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree73Norm x).property (boundaryFullPowerDegree73Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree73Norm,boundaryFullPowerDegree73Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))=c} := by

  have he : ((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))=(boundaryRePowerRow77_21Degree73Norm x).val+(boundaryRePowerRow77_22Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree73Norm x).property (boundaryRePowerRow77_22Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree73Norm,boundaryRePowerRow77_22Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))=(boundaryRePowerRow77_20Degree73Norm x).val+(boundaryFullPowerDegree73Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree73Norm x).property (boundaryFullPowerDegree73Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree73Norm,boundaryFullPowerDegree73Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))))=(boundaryFullPowerDegree73Block16Norm x).val+(boundaryFullPowerDegree73Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block16Norm x).property (boundaryFullPowerDegree73Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block16Norm,boundaryFullPowerDegree73Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))))))=(boundaryFullPowerDegree73Block14Norm x).val+(boundaryFullPowerDegree73Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block14Norm x).property (boundaryFullPowerDegree73Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block14Norm,boundaryFullPowerDegree73Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x)))))))))+(((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x)))))))))+(((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x))))))))))=(boundaryFullPowerDegree73Block9Norm x).val+(boundaryFullPowerDegree73Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block9Norm x).property (boundaryFullPowerDegree73Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block9Norm,boundaryFullPowerDegree73Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x))=c} := by

  have he : ((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x))=(boundaryImPowerRow77_0Degree73Norm x).val+(boundaryImPowerRow77_1Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree73Norm x).property (boundaryImPowerRow77_1Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree73Norm,boundaryImPowerRow77_1Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x))=c} := by

  have he : ((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x))=(boundaryImPowerRow77_3Degree73Norm x).val+(boundaryImPowerRow77_4Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree73Norm x).property (boundaryImPowerRow77_4Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree73Norm,boundaryImPowerRow77_4Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x))))=(boundaryImPowerRow77_2Degree73Norm x).val+(boundaryFullPowerDegree73Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree73Norm x).property (boundaryFullPowerDegree73Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree73Norm,boundaryFullPowerDegree73Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x))))))=(boundaryFullPowerDegree73Block22Norm x).val+(boundaryFullPowerDegree73Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block22Norm x).property (boundaryFullPowerDegree73Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block22Norm,boundaryFullPowerDegree73Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x))=c} := by

  have he : ((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x))=(boundaryImPowerRow77_6Degree73Norm x).val+(boundaryImPowerRow77_7Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree73Norm x).property (boundaryImPowerRow77_7Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree73Norm,boundaryImPowerRow77_7Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x))))=(boundaryImPowerRow77_5Degree73Norm x).val+(boundaryFullPowerDegree73Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree73Norm x).property (boundaryFullPowerDegree73Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree73Norm,boundaryFullPowerDegree73Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))=c} := by

  have he : ((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))=(boundaryImPowerRow77_9Degree73Norm x).val+(boundaryImPowerRow77_10Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree73Norm x).property (boundaryImPowerRow77_10Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree73Norm,boundaryImPowerRow77_10Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))))=(boundaryImPowerRow77_8Degree73Norm x).val+(boundaryFullPowerDegree73Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree73Norm x).property (boundaryFullPowerDegree73Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree73Norm,boundaryFullPowerDegree73Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))))))=(boundaryFullPowerDegree73Block27Norm x).val+(boundaryFullPowerDegree73Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block27Norm x).property (boundaryFullPowerDegree73Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block27Norm,boundaryFullPowerDegree73Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x))))))))=(boundaryFullPowerDegree73Block25Norm x).val+(boundaryFullPowerDegree73Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block25Norm x).property (boundaryFullPowerDegree73Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block25Norm,boundaryFullPowerDegree73Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x))=c} := by

  have he : ((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x))=(boundaryImPowerRow77_12Degree73Norm x).val+(boundaryImPowerRow77_13Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree73Norm x).property (boundaryImPowerRow77_13Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree73Norm,boundaryImPowerRow77_13Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x))))=(boundaryImPowerRow77_11Degree73Norm x).val+(boundaryFullPowerDegree73Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree73Norm x).property (boundaryFullPowerDegree73Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree73Norm,boundaryFullPowerDegree73Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x))=c} := by

  have he : ((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x))=(boundaryImPowerRow77_15Degree73Norm x).val+(boundaryImPowerRow77_16Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree73Norm x).property (boundaryImPowerRow77_16Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree73Norm,boundaryImPowerRow77_16Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x))))=(boundaryImPowerRow77_14Degree73Norm x).val+(boundaryFullPowerDegree73Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree73Norm x).property (boundaryFullPowerDegree73Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree73Norm,boundaryFullPowerDegree73Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x))))))=(boundaryFullPowerDegree73Block33Norm x).val+(boundaryFullPowerDegree73Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block33Norm x).property (boundaryFullPowerDegree73Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block33Norm,boundaryFullPowerDegree73Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x))=c} := by

  have he : ((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x))=(boundaryImPowerRow77_18Degree73Norm x).val+(boundaryImPowerRow77_19Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree73Norm x).property (boundaryImPowerRow77_19Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree73Norm,boundaryImPowerRow77_19Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x))))=(boundaryImPowerRow77_17Degree73Norm x).val+(boundaryFullPowerDegree73Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree73Norm x).property (boundaryFullPowerDegree73Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree73Norm,boundaryFullPowerDegree73Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))=c} := by

  have he : ((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))=(boundaryImPowerRow77_21Degree73Norm x).val+(boundaryLowPowerRow77Degree73Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree73Norm x).property (boundaryLowPowerRow77Degree73Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree73Norm,boundaryLowPowerRow77Degree73Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))=(boundaryImPowerRow77_20Degree73Norm x).val+(boundaryFullPowerDegree73Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree73Norm x).property (boundaryFullPowerDegree73Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree73Norm,boundaryFullPowerDegree73Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))=(boundaryFullPowerDegree73Block38Norm x).val+(boundaryFullPowerDegree73Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block38Norm x).property (boundaryFullPowerDegree73Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block38Norm,boundaryFullPowerDegree73Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))))=(boundaryFullPowerDegree73Block36Norm x).val+(boundaryFullPowerDegree73Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block36Norm x).property (boundaryFullPowerDegree73Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block36Norm,boundaryFullPowerDegree73Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x)))))))))+(((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x)))))))))+(((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))))))=(boundaryFullPowerDegree73Block31Norm x).val+(boundaryFullPowerDegree73Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block31Norm x).property (boundaryFullPowerDegree73Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block31Norm,boundaryFullPowerDegree73Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree73Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x)))))))))+(((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x)))))))))))+(((((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x)))))))))+(((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x)))))))))+(((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x)))))))))))+(((((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x)))))))))+(((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x))))))))))))=(boundaryFullPowerDegree73Block21Norm x).val+(boundaryFullPowerDegree73Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree73Block21Norm x).property (boundaryFullPowerDegree73Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block21Norm,boundaryFullPowerDegree73Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree73Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 73 x=c} := by

  have he0 : boundaryFullPowerRow77 73 x=((((((((((boundaryRePowerRow77_0 73 x)+(boundaryRePowerRow77_1 73 x)))+(((boundaryRePowerRow77_2 73 x)+(((boundaryRePowerRow77_3 73 x)+(boundaryRePowerRow77_4 73 x)))))))+(((((boundaryRePowerRow77_5 73 x)+(((boundaryRePowerRow77_6 73 x)+(boundaryRePowerRow77_7 73 x)))))+(((boundaryRePowerRow77_8 73 x)+(((boundaryRePowerRow77_9 73 x)+(boundaryRePowerRow77_10 73 x)))))))))+(((((((boundaryRePowerRow77_11 73 x)+(((boundaryRePowerRow77_12 73 x)+(boundaryRePowerRow77_13 73 x)))))+(((boundaryRePowerRow77_14 73 x)+(((boundaryRePowerRow77_15 73 x)+(boundaryRePowerRow77_16 73 x)))))))+(((((boundaryRePowerRow77_17 73 x)+(((boundaryRePowerRow77_18 73 x)+(boundaryRePowerRow77_19 73 x)))))+(((boundaryRePowerRow77_20 73 x)+(((boundaryRePowerRow77_21 73 x)+(boundaryRePowerRow77_22 73 x)))))))))))+(((((((((boundaryImPowerRow77_0 73 x)+(boundaryImPowerRow77_1 73 x)))+(((boundaryImPowerRow77_2 73 x)+(((boundaryImPowerRow77_3 73 x)+(boundaryImPowerRow77_4 73 x)))))))+(((((boundaryImPowerRow77_5 73 x)+(((boundaryImPowerRow77_6 73 x)+(boundaryImPowerRow77_7 73 x)))))+(((boundaryImPowerRow77_8 73 x)+(((boundaryImPowerRow77_9 73 x)+(boundaryImPowerRow77_10 73 x)))))))))+(((((((boundaryImPowerRow77_11 73 x)+(((boundaryImPowerRow77_12 73 x)+(boundaryImPowerRow77_13 73 x)))))+(((boundaryImPowerRow77_14 73 x)+(((boundaryImPowerRow77_15 73 x)+(boundaryImPowerRow77_16 73 x)))))))+(((((boundaryImPowerRow77_17 73 x)+(((boundaryImPowerRow77_18 73 x)+(boundaryImPowerRow77_19 73 x)))))+(((boundaryImPowerRow77_20 73 x)+(((boundaryImPowerRow77_21 73 x)+(boundaryLowPowerRow77 73 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree73Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree73Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
