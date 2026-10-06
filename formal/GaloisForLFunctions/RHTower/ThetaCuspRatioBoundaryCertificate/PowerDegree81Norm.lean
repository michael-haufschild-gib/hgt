import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree81Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree81Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x))=c} := by

  have he : ((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x))=(boundaryRePowerRow77_0Degree81Norm x).val+(boundaryRePowerRow77_1Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree81Norm x).property (boundaryRePowerRow77_1Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree81Norm,boundaryRePowerRow77_1Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x))=c} := by

  have he : ((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x))=(boundaryRePowerRow77_3Degree81Norm x).val+(boundaryRePowerRow77_4Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree81Norm x).property (boundaryRePowerRow77_4Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree81Norm,boundaryRePowerRow77_4Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x))))=(boundaryRePowerRow77_2Degree81Norm x).val+(boundaryFullPowerDegree81Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree81Norm x).property (boundaryFullPowerDegree81Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree81Norm,boundaryFullPowerDegree81Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x))))))=(boundaryFullPowerDegree81Block0Norm x).val+(boundaryFullPowerDegree81Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block0Norm x).property (boundaryFullPowerDegree81Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block0Norm,boundaryFullPowerDegree81Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x))=c} := by

  have he : ((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x))=(boundaryRePowerRow77_6Degree81Norm x).val+(boundaryRePowerRow77_7Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree81Norm x).property (boundaryRePowerRow77_7Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree81Norm,boundaryRePowerRow77_7Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x))))=(boundaryRePowerRow77_5Degree81Norm x).val+(boundaryFullPowerDegree81Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree81Norm x).property (boundaryFullPowerDegree81Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree81Norm,boundaryFullPowerDegree81Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))=c} := by

  have he : ((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))=(boundaryRePowerRow77_9Degree81Norm x).val+(boundaryRePowerRow77_10Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree81Norm x).property (boundaryRePowerRow77_10Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree81Norm,boundaryRePowerRow77_10Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))))=(boundaryRePowerRow77_8Degree81Norm x).val+(boundaryFullPowerDegree81Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree81Norm x).property (boundaryFullPowerDegree81Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree81Norm,boundaryFullPowerDegree81Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))))))=(boundaryFullPowerDegree81Block5Norm x).val+(boundaryFullPowerDegree81Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block5Norm x).property (boundaryFullPowerDegree81Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block5Norm,boundaryFullPowerDegree81Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x))))))))=(boundaryFullPowerDegree81Block3Norm x).val+(boundaryFullPowerDegree81Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block3Norm x).property (boundaryFullPowerDegree81Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block3Norm,boundaryFullPowerDegree81Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x))=c} := by

  have he : ((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x))=(boundaryRePowerRow77_12Degree81Norm x).val+(boundaryRePowerRow77_13Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree81Norm x).property (boundaryRePowerRow77_13Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree81Norm,boundaryRePowerRow77_13Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x))))=(boundaryRePowerRow77_11Degree81Norm x).val+(boundaryFullPowerDegree81Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree81Norm x).property (boundaryFullPowerDegree81Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree81Norm,boundaryFullPowerDegree81Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x))=c} := by

  have he : ((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x))=(boundaryRePowerRow77_15Degree81Norm x).val+(boundaryRePowerRow77_16Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree81Norm x).property (boundaryRePowerRow77_16Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree81Norm,boundaryRePowerRow77_16Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x))))=(boundaryRePowerRow77_14Degree81Norm x).val+(boundaryFullPowerDegree81Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree81Norm x).property (boundaryFullPowerDegree81Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree81Norm,boundaryFullPowerDegree81Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x))))))=(boundaryFullPowerDegree81Block11Norm x).val+(boundaryFullPowerDegree81Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block11Norm x).property (boundaryFullPowerDegree81Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block11Norm,boundaryFullPowerDegree81Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x))=c} := by

  have he : ((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x))=(boundaryRePowerRow77_18Degree81Norm x).val+(boundaryRePowerRow77_19Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree81Norm x).property (boundaryRePowerRow77_19Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree81Norm,boundaryRePowerRow77_19Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x))))=(boundaryRePowerRow77_17Degree81Norm x).val+(boundaryFullPowerDegree81Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree81Norm x).property (boundaryFullPowerDegree81Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree81Norm,boundaryFullPowerDegree81Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))=c} := by

  have he : ((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))=(boundaryRePowerRow77_21Degree81Norm x).val+(boundaryRePowerRow77_22Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree81Norm x).property (boundaryRePowerRow77_22Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree81Norm,boundaryRePowerRow77_22Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))=(boundaryRePowerRow77_20Degree81Norm x).val+(boundaryFullPowerDegree81Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree81Norm x).property (boundaryFullPowerDegree81Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree81Norm,boundaryFullPowerDegree81Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))))=(boundaryFullPowerDegree81Block16Norm x).val+(boundaryFullPowerDegree81Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block16Norm x).property (boundaryFullPowerDegree81Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block16Norm,boundaryFullPowerDegree81Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))))))=(boundaryFullPowerDegree81Block14Norm x).val+(boundaryFullPowerDegree81Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block14Norm x).property (boundaryFullPowerDegree81Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block14Norm,boundaryFullPowerDegree81Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x)))))))))+(((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x)))))))))+(((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x))))))))))=(boundaryFullPowerDegree81Block9Norm x).val+(boundaryFullPowerDegree81Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block9Norm x).property (boundaryFullPowerDegree81Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block9Norm,boundaryFullPowerDegree81Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x))=c} := by

  have he : ((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x))=(boundaryImPowerRow77_0Degree81Norm x).val+(boundaryImPowerRow77_1Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree81Norm x).property (boundaryImPowerRow77_1Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree81Norm,boundaryImPowerRow77_1Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x))=c} := by

  have he : ((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x))=(boundaryImPowerRow77_3Degree81Norm x).val+(boundaryImPowerRow77_4Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree81Norm x).property (boundaryImPowerRow77_4Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree81Norm,boundaryImPowerRow77_4Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x))))=(boundaryImPowerRow77_2Degree81Norm x).val+(boundaryFullPowerDegree81Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree81Norm x).property (boundaryFullPowerDegree81Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree81Norm,boundaryFullPowerDegree81Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x))))))=(boundaryFullPowerDegree81Block22Norm x).val+(boundaryFullPowerDegree81Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block22Norm x).property (boundaryFullPowerDegree81Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block22Norm,boundaryFullPowerDegree81Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x))=c} := by

  have he : ((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x))=(boundaryImPowerRow77_6Degree81Norm x).val+(boundaryImPowerRow77_7Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree81Norm x).property (boundaryImPowerRow77_7Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree81Norm,boundaryImPowerRow77_7Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x))))=(boundaryImPowerRow77_5Degree81Norm x).val+(boundaryFullPowerDegree81Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree81Norm x).property (boundaryFullPowerDegree81Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree81Norm,boundaryFullPowerDegree81Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))=c} := by

  have he : ((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))=(boundaryImPowerRow77_9Degree81Norm x).val+(boundaryImPowerRow77_10Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree81Norm x).property (boundaryImPowerRow77_10Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree81Norm,boundaryImPowerRow77_10Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))))=(boundaryImPowerRow77_8Degree81Norm x).val+(boundaryFullPowerDegree81Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree81Norm x).property (boundaryFullPowerDegree81Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree81Norm,boundaryFullPowerDegree81Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))))))=(boundaryFullPowerDegree81Block27Norm x).val+(boundaryFullPowerDegree81Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block27Norm x).property (boundaryFullPowerDegree81Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block27Norm,boundaryFullPowerDegree81Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x))))))))=(boundaryFullPowerDegree81Block25Norm x).val+(boundaryFullPowerDegree81Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block25Norm x).property (boundaryFullPowerDegree81Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block25Norm,boundaryFullPowerDegree81Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x))=c} := by

  have he : ((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x))=(boundaryImPowerRow77_12Degree81Norm x).val+(boundaryImPowerRow77_13Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree81Norm x).property (boundaryImPowerRow77_13Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree81Norm,boundaryImPowerRow77_13Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x))))=(boundaryImPowerRow77_11Degree81Norm x).val+(boundaryFullPowerDegree81Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree81Norm x).property (boundaryFullPowerDegree81Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree81Norm,boundaryFullPowerDegree81Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x))=c} := by

  have he : ((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x))=(boundaryImPowerRow77_15Degree81Norm x).val+(boundaryImPowerRow77_16Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree81Norm x).property (boundaryImPowerRow77_16Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree81Norm,boundaryImPowerRow77_16Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x))))=(boundaryImPowerRow77_14Degree81Norm x).val+(boundaryFullPowerDegree81Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree81Norm x).property (boundaryFullPowerDegree81Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree81Norm,boundaryFullPowerDegree81Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x))))))=(boundaryFullPowerDegree81Block33Norm x).val+(boundaryFullPowerDegree81Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block33Norm x).property (boundaryFullPowerDegree81Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block33Norm,boundaryFullPowerDegree81Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x))=c} := by

  have he : ((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x))=(boundaryImPowerRow77_18Degree81Norm x).val+(boundaryImPowerRow77_19Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree81Norm x).property (boundaryImPowerRow77_19Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree81Norm,boundaryImPowerRow77_19Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x))))=(boundaryImPowerRow77_17Degree81Norm x).val+(boundaryFullPowerDegree81Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree81Norm x).property (boundaryFullPowerDegree81Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree81Norm,boundaryFullPowerDegree81Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))=c} := by

  have he : ((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))=(boundaryImPowerRow77_21Degree81Norm x).val+(boundaryLowPowerRow77Degree81Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree81Norm x).property (boundaryLowPowerRow77Degree81Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree81Norm,boundaryLowPowerRow77Degree81Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))=(boundaryImPowerRow77_20Degree81Norm x).val+(boundaryFullPowerDegree81Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree81Norm x).property (boundaryFullPowerDegree81Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree81Norm,boundaryFullPowerDegree81Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))=(boundaryFullPowerDegree81Block38Norm x).val+(boundaryFullPowerDegree81Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block38Norm x).property (boundaryFullPowerDegree81Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block38Norm,boundaryFullPowerDegree81Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))))=(boundaryFullPowerDegree81Block36Norm x).val+(boundaryFullPowerDegree81Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block36Norm x).property (boundaryFullPowerDegree81Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block36Norm,boundaryFullPowerDegree81Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x)))))))))+(((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x)))))))))+(((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))))))=(boundaryFullPowerDegree81Block31Norm x).val+(boundaryFullPowerDegree81Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block31Norm x).property (boundaryFullPowerDegree81Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block31Norm,boundaryFullPowerDegree81Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree81Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x)))))))))+(((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x)))))))))))+(((((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x)))))))))+(((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x)))))))))+(((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x)))))))))))+(((((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x)))))))))+(((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x))))))))))))=(boundaryFullPowerDegree81Block21Norm x).val+(boundaryFullPowerDegree81Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree81Block21Norm x).property (boundaryFullPowerDegree81Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block21Norm,boundaryFullPowerDegree81Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree81Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 81 x=c} := by

  have he0 : boundaryFullPowerRow77 81 x=((((((((((boundaryRePowerRow77_0 81 x)+(boundaryRePowerRow77_1 81 x)))+(((boundaryRePowerRow77_2 81 x)+(((boundaryRePowerRow77_3 81 x)+(boundaryRePowerRow77_4 81 x)))))))+(((((boundaryRePowerRow77_5 81 x)+(((boundaryRePowerRow77_6 81 x)+(boundaryRePowerRow77_7 81 x)))))+(((boundaryRePowerRow77_8 81 x)+(((boundaryRePowerRow77_9 81 x)+(boundaryRePowerRow77_10 81 x)))))))))+(((((((boundaryRePowerRow77_11 81 x)+(((boundaryRePowerRow77_12 81 x)+(boundaryRePowerRow77_13 81 x)))))+(((boundaryRePowerRow77_14 81 x)+(((boundaryRePowerRow77_15 81 x)+(boundaryRePowerRow77_16 81 x)))))))+(((((boundaryRePowerRow77_17 81 x)+(((boundaryRePowerRow77_18 81 x)+(boundaryRePowerRow77_19 81 x)))))+(((boundaryRePowerRow77_20 81 x)+(((boundaryRePowerRow77_21 81 x)+(boundaryRePowerRow77_22 81 x)))))))))))+(((((((((boundaryImPowerRow77_0 81 x)+(boundaryImPowerRow77_1 81 x)))+(((boundaryImPowerRow77_2 81 x)+(((boundaryImPowerRow77_3 81 x)+(boundaryImPowerRow77_4 81 x)))))))+(((((boundaryImPowerRow77_5 81 x)+(((boundaryImPowerRow77_6 81 x)+(boundaryImPowerRow77_7 81 x)))))+(((boundaryImPowerRow77_8 81 x)+(((boundaryImPowerRow77_9 81 x)+(boundaryImPowerRow77_10 81 x)))))))))+(((((((boundaryImPowerRow77_11 81 x)+(((boundaryImPowerRow77_12 81 x)+(boundaryImPowerRow77_13 81 x)))))+(((boundaryImPowerRow77_14 81 x)+(((boundaryImPowerRow77_15 81 x)+(boundaryImPowerRow77_16 81 x)))))))+(((((boundaryImPowerRow77_17 81 x)+(((boundaryImPowerRow77_18 81 x)+(boundaryImPowerRow77_19 81 x)))))+(((boundaryImPowerRow77_20 81 x)+(((boundaryImPowerRow77_21 81 x)+(boundaryLowPowerRow77 81 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree81Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree81Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
