import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree42Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree42Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x))=c} := by

  have he : ((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x))=(boundaryRePowerRow77_0Degree42Norm x).val+(boundaryRePowerRow77_1Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree42Norm x).property (boundaryRePowerRow77_1Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree42Norm,boundaryRePowerRow77_1Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x))=c} := by

  have he : ((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x))=(boundaryRePowerRow77_3Degree42Norm x).val+(boundaryRePowerRow77_4Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree42Norm x).property (boundaryRePowerRow77_4Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree42Norm,boundaryRePowerRow77_4Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x))))=(boundaryRePowerRow77_2Degree42Norm x).val+(boundaryFullPowerDegree42Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree42Norm x).property (boundaryFullPowerDegree42Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree42Norm,boundaryFullPowerDegree42Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x))))))=(boundaryFullPowerDegree42Block0Norm x).val+(boundaryFullPowerDegree42Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block0Norm x).property (boundaryFullPowerDegree42Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block0Norm,boundaryFullPowerDegree42Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x))=c} := by

  have he : ((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x))=(boundaryRePowerRow77_6Degree42Norm x).val+(boundaryRePowerRow77_7Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree42Norm x).property (boundaryRePowerRow77_7Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree42Norm,boundaryRePowerRow77_7Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x))))=(boundaryRePowerRow77_5Degree42Norm x).val+(boundaryFullPowerDegree42Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree42Norm x).property (boundaryFullPowerDegree42Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree42Norm,boundaryFullPowerDegree42Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))=c} := by

  have he : ((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))=(boundaryRePowerRow77_9Degree42Norm x).val+(boundaryRePowerRow77_10Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree42Norm x).property (boundaryRePowerRow77_10Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree42Norm,boundaryRePowerRow77_10Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))))=(boundaryRePowerRow77_8Degree42Norm x).val+(boundaryFullPowerDegree42Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree42Norm x).property (boundaryFullPowerDegree42Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree42Norm,boundaryFullPowerDegree42Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))))))=(boundaryFullPowerDegree42Block5Norm x).val+(boundaryFullPowerDegree42Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block5Norm x).property (boundaryFullPowerDegree42Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block5Norm,boundaryFullPowerDegree42Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x))))))))=(boundaryFullPowerDegree42Block3Norm x).val+(boundaryFullPowerDegree42Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block3Norm x).property (boundaryFullPowerDegree42Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block3Norm,boundaryFullPowerDegree42Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x))=c} := by

  have he : ((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x))=(boundaryRePowerRow77_12Degree42Norm x).val+(boundaryRePowerRow77_13Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree42Norm x).property (boundaryRePowerRow77_13Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree42Norm,boundaryRePowerRow77_13Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x))))=(boundaryRePowerRow77_11Degree42Norm x).val+(boundaryFullPowerDegree42Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree42Norm x).property (boundaryFullPowerDegree42Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree42Norm,boundaryFullPowerDegree42Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x))=c} := by

  have he : ((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x))=(boundaryRePowerRow77_15Degree42Norm x).val+(boundaryRePowerRow77_16Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree42Norm x).property (boundaryRePowerRow77_16Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree42Norm,boundaryRePowerRow77_16Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x))))=(boundaryRePowerRow77_14Degree42Norm x).val+(boundaryFullPowerDegree42Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree42Norm x).property (boundaryFullPowerDegree42Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree42Norm,boundaryFullPowerDegree42Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x))))))=(boundaryFullPowerDegree42Block11Norm x).val+(boundaryFullPowerDegree42Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block11Norm x).property (boundaryFullPowerDegree42Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block11Norm,boundaryFullPowerDegree42Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x))=c} := by

  have he : ((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x))=(boundaryRePowerRow77_18Degree42Norm x).val+(boundaryRePowerRow77_19Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree42Norm x).property (boundaryRePowerRow77_19Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree42Norm,boundaryRePowerRow77_19Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x))))=(boundaryRePowerRow77_17Degree42Norm x).val+(boundaryFullPowerDegree42Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree42Norm x).property (boundaryFullPowerDegree42Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree42Norm,boundaryFullPowerDegree42Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))=c} := by

  have he : ((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))=(boundaryRePowerRow77_21Degree42Norm x).val+(boundaryRePowerRow77_22Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree42Norm x).property (boundaryRePowerRow77_22Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree42Norm,boundaryRePowerRow77_22Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))=(boundaryRePowerRow77_20Degree42Norm x).val+(boundaryFullPowerDegree42Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree42Norm x).property (boundaryFullPowerDegree42Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree42Norm,boundaryFullPowerDegree42Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))))=(boundaryFullPowerDegree42Block16Norm x).val+(boundaryFullPowerDegree42Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block16Norm x).property (boundaryFullPowerDegree42Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block16Norm,boundaryFullPowerDegree42Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))))))=(boundaryFullPowerDegree42Block14Norm x).val+(boundaryFullPowerDegree42Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block14Norm x).property (boundaryFullPowerDegree42Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block14Norm,boundaryFullPowerDegree42Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x)))))))))+(((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x)))))))))+(((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x))))))))))=(boundaryFullPowerDegree42Block9Norm x).val+(boundaryFullPowerDegree42Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block9Norm x).property (boundaryFullPowerDegree42Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block9Norm,boundaryFullPowerDegree42Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x))=c} := by

  have he : ((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x))=(boundaryImPowerRow77_0Degree42Norm x).val+(boundaryImPowerRow77_1Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree42Norm x).property (boundaryImPowerRow77_1Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree42Norm,boundaryImPowerRow77_1Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x))=c} := by

  have he : ((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x))=(boundaryImPowerRow77_3Degree42Norm x).val+(boundaryImPowerRow77_4Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree42Norm x).property (boundaryImPowerRow77_4Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree42Norm,boundaryImPowerRow77_4Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x))))=(boundaryImPowerRow77_2Degree42Norm x).val+(boundaryFullPowerDegree42Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree42Norm x).property (boundaryFullPowerDegree42Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree42Norm,boundaryFullPowerDegree42Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x))))))=(boundaryFullPowerDegree42Block22Norm x).val+(boundaryFullPowerDegree42Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block22Norm x).property (boundaryFullPowerDegree42Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block22Norm,boundaryFullPowerDegree42Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x))=c} := by

  have he : ((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x))=(boundaryImPowerRow77_6Degree42Norm x).val+(boundaryImPowerRow77_7Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree42Norm x).property (boundaryImPowerRow77_7Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree42Norm,boundaryImPowerRow77_7Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x))))=(boundaryImPowerRow77_5Degree42Norm x).val+(boundaryFullPowerDegree42Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree42Norm x).property (boundaryFullPowerDegree42Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree42Norm,boundaryFullPowerDegree42Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))=c} := by

  have he : ((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))=(boundaryImPowerRow77_9Degree42Norm x).val+(boundaryImPowerRow77_10Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree42Norm x).property (boundaryImPowerRow77_10Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree42Norm,boundaryImPowerRow77_10Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))))=(boundaryImPowerRow77_8Degree42Norm x).val+(boundaryFullPowerDegree42Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree42Norm x).property (boundaryFullPowerDegree42Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree42Norm,boundaryFullPowerDegree42Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))))))=(boundaryFullPowerDegree42Block27Norm x).val+(boundaryFullPowerDegree42Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block27Norm x).property (boundaryFullPowerDegree42Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block27Norm,boundaryFullPowerDegree42Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x))))))))=(boundaryFullPowerDegree42Block25Norm x).val+(boundaryFullPowerDegree42Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block25Norm x).property (boundaryFullPowerDegree42Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block25Norm,boundaryFullPowerDegree42Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x))=c} := by

  have he : ((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x))=(boundaryImPowerRow77_12Degree42Norm x).val+(boundaryImPowerRow77_13Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree42Norm x).property (boundaryImPowerRow77_13Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree42Norm,boundaryImPowerRow77_13Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x))))=(boundaryImPowerRow77_11Degree42Norm x).val+(boundaryFullPowerDegree42Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree42Norm x).property (boundaryFullPowerDegree42Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree42Norm,boundaryFullPowerDegree42Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x))=c} := by

  have he : ((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x))=(boundaryImPowerRow77_15Degree42Norm x).val+(boundaryImPowerRow77_16Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree42Norm x).property (boundaryImPowerRow77_16Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree42Norm,boundaryImPowerRow77_16Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x))))=(boundaryImPowerRow77_14Degree42Norm x).val+(boundaryFullPowerDegree42Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree42Norm x).property (boundaryFullPowerDegree42Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree42Norm,boundaryFullPowerDegree42Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x))))))=(boundaryFullPowerDegree42Block33Norm x).val+(boundaryFullPowerDegree42Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block33Norm x).property (boundaryFullPowerDegree42Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block33Norm,boundaryFullPowerDegree42Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x))=c} := by

  have he : ((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x))=(boundaryImPowerRow77_18Degree42Norm x).val+(boundaryImPowerRow77_19Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree42Norm x).property (boundaryImPowerRow77_19Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree42Norm,boundaryImPowerRow77_19Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x))))=(boundaryImPowerRow77_17Degree42Norm x).val+(boundaryFullPowerDegree42Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree42Norm x).property (boundaryFullPowerDegree42Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree42Norm,boundaryFullPowerDegree42Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))=c} := by

  have he : ((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))=(boundaryImPowerRow77_21Degree42Norm x).val+(boundaryLowPowerRow77Degree42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree42Norm x).property (boundaryLowPowerRow77Degree42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree42Norm,boundaryLowPowerRow77Degree42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))=(boundaryImPowerRow77_20Degree42Norm x).val+(boundaryFullPowerDegree42Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree42Norm x).property (boundaryFullPowerDegree42Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree42Norm,boundaryFullPowerDegree42Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))=(boundaryFullPowerDegree42Block38Norm x).val+(boundaryFullPowerDegree42Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block38Norm x).property (boundaryFullPowerDegree42Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block38Norm,boundaryFullPowerDegree42Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))))=(boundaryFullPowerDegree42Block36Norm x).val+(boundaryFullPowerDegree42Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block36Norm x).property (boundaryFullPowerDegree42Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block36Norm,boundaryFullPowerDegree42Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x)))))))))+(((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x)))))))))+(((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))))))=(boundaryFullPowerDegree42Block31Norm x).val+(boundaryFullPowerDegree42Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block31Norm x).property (boundaryFullPowerDegree42Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block31Norm,boundaryFullPowerDegree42Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree42Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x)))))))))+(((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x)))))))))))+(((((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x)))))))))+(((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x)))))))))+(((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x)))))))))))+(((((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x)))))))))+(((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x))))))))))))=(boundaryFullPowerDegree42Block21Norm x).val+(boundaryFullPowerDegree42Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree42Block21Norm x).property (boundaryFullPowerDegree42Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block21Norm,boundaryFullPowerDegree42Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree42Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 42 x=c} := by

  have he0 : boundaryFullPowerRow77 42 x=((((((((((boundaryRePowerRow77_0 42 x)+(boundaryRePowerRow77_1 42 x)))+(((boundaryRePowerRow77_2 42 x)+(((boundaryRePowerRow77_3 42 x)+(boundaryRePowerRow77_4 42 x)))))))+(((((boundaryRePowerRow77_5 42 x)+(((boundaryRePowerRow77_6 42 x)+(boundaryRePowerRow77_7 42 x)))))+(((boundaryRePowerRow77_8 42 x)+(((boundaryRePowerRow77_9 42 x)+(boundaryRePowerRow77_10 42 x)))))))))+(((((((boundaryRePowerRow77_11 42 x)+(((boundaryRePowerRow77_12 42 x)+(boundaryRePowerRow77_13 42 x)))))+(((boundaryRePowerRow77_14 42 x)+(((boundaryRePowerRow77_15 42 x)+(boundaryRePowerRow77_16 42 x)))))))+(((((boundaryRePowerRow77_17 42 x)+(((boundaryRePowerRow77_18 42 x)+(boundaryRePowerRow77_19 42 x)))))+(((boundaryRePowerRow77_20 42 x)+(((boundaryRePowerRow77_21 42 x)+(boundaryRePowerRow77_22 42 x)))))))))))+(((((((((boundaryImPowerRow77_0 42 x)+(boundaryImPowerRow77_1 42 x)))+(((boundaryImPowerRow77_2 42 x)+(((boundaryImPowerRow77_3 42 x)+(boundaryImPowerRow77_4 42 x)))))))+(((((boundaryImPowerRow77_5 42 x)+(((boundaryImPowerRow77_6 42 x)+(boundaryImPowerRow77_7 42 x)))))+(((boundaryImPowerRow77_8 42 x)+(((boundaryImPowerRow77_9 42 x)+(boundaryImPowerRow77_10 42 x)))))))))+(((((((boundaryImPowerRow77_11 42 x)+(((boundaryImPowerRow77_12 42 x)+(boundaryImPowerRow77_13 42 x)))))+(((boundaryImPowerRow77_14 42 x)+(((boundaryImPowerRow77_15 42 x)+(boundaryImPowerRow77_16 42 x)))))))+(((((boundaryImPowerRow77_17 42 x)+(((boundaryImPowerRow77_18 42 x)+(boundaryImPowerRow77_19 42 x)))))+(((boundaryImPowerRow77_20 42 x)+(((boundaryImPowerRow77_21 42 x)+(boundaryLowPowerRow77 42 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree42Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree42Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
