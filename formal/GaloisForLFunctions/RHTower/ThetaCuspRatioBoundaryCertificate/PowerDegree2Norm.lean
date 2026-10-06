import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree2Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree2Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x))=c} := by

  have he : ((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x))=(boundaryRePowerRow77_0Degree2Norm x).val+(boundaryRePowerRow77_1Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree2Norm x).property (boundaryRePowerRow77_1Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree2Norm,boundaryRePowerRow77_1Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x))=c} := by

  have he : ((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x))=(boundaryRePowerRow77_3Degree2Norm x).val+(boundaryRePowerRow77_4Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree2Norm x).property (boundaryRePowerRow77_4Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree2Norm,boundaryRePowerRow77_4Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x))))=(boundaryRePowerRow77_2Degree2Norm x).val+(boundaryFullPowerDegree2Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree2Norm x).property (boundaryFullPowerDegree2Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree2Norm,boundaryFullPowerDegree2Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x))))))=(boundaryFullPowerDegree2Block0Norm x).val+(boundaryFullPowerDegree2Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block0Norm x).property (boundaryFullPowerDegree2Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block0Norm,boundaryFullPowerDegree2Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x))=c} := by

  have he : ((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x))=(boundaryRePowerRow77_6Degree2Norm x).val+(boundaryRePowerRow77_7Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree2Norm x).property (boundaryRePowerRow77_7Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree2Norm,boundaryRePowerRow77_7Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x))))=(boundaryRePowerRow77_5Degree2Norm x).val+(boundaryFullPowerDegree2Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree2Norm x).property (boundaryFullPowerDegree2Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree2Norm,boundaryFullPowerDegree2Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))=c} := by

  have he : ((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))=(boundaryRePowerRow77_9Degree2Norm x).val+(boundaryRePowerRow77_10Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree2Norm x).property (boundaryRePowerRow77_10Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree2Norm,boundaryRePowerRow77_10Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))))=(boundaryRePowerRow77_8Degree2Norm x).val+(boundaryFullPowerDegree2Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree2Norm x).property (boundaryFullPowerDegree2Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree2Norm,boundaryFullPowerDegree2Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))))))=(boundaryFullPowerDegree2Block5Norm x).val+(boundaryFullPowerDegree2Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block5Norm x).property (boundaryFullPowerDegree2Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block5Norm,boundaryFullPowerDegree2Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x))))))))=(boundaryFullPowerDegree2Block3Norm x).val+(boundaryFullPowerDegree2Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block3Norm x).property (boundaryFullPowerDegree2Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block3Norm,boundaryFullPowerDegree2Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x))=c} := by

  have he : ((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x))=(boundaryRePowerRow77_12Degree2Norm x).val+(boundaryRePowerRow77_13Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree2Norm x).property (boundaryRePowerRow77_13Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree2Norm,boundaryRePowerRow77_13Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x))))=(boundaryRePowerRow77_11Degree2Norm x).val+(boundaryFullPowerDegree2Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree2Norm x).property (boundaryFullPowerDegree2Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree2Norm,boundaryFullPowerDegree2Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x))=c} := by

  have he : ((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x))=(boundaryRePowerRow77_15Degree2Norm x).val+(boundaryRePowerRow77_16Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree2Norm x).property (boundaryRePowerRow77_16Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree2Norm,boundaryRePowerRow77_16Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x))))=(boundaryRePowerRow77_14Degree2Norm x).val+(boundaryFullPowerDegree2Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree2Norm x).property (boundaryFullPowerDegree2Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree2Norm,boundaryFullPowerDegree2Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x))))))=(boundaryFullPowerDegree2Block11Norm x).val+(boundaryFullPowerDegree2Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block11Norm x).property (boundaryFullPowerDegree2Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block11Norm,boundaryFullPowerDegree2Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x))=c} := by

  have he : ((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x))=(boundaryRePowerRow77_18Degree2Norm x).val+(boundaryRePowerRow77_19Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree2Norm x).property (boundaryRePowerRow77_19Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree2Norm,boundaryRePowerRow77_19Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x))))=(boundaryRePowerRow77_17Degree2Norm x).val+(boundaryFullPowerDegree2Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree2Norm x).property (boundaryFullPowerDegree2Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree2Norm,boundaryFullPowerDegree2Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))=c} := by

  have he : ((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))=(boundaryRePowerRow77_21Degree2Norm x).val+(boundaryRePowerRow77_22Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree2Norm x).property (boundaryRePowerRow77_22Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree2Norm,boundaryRePowerRow77_22Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))=(boundaryRePowerRow77_20Degree2Norm x).val+(boundaryFullPowerDegree2Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree2Norm x).property (boundaryFullPowerDegree2Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree2Norm,boundaryFullPowerDegree2Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))))=(boundaryFullPowerDegree2Block16Norm x).val+(boundaryFullPowerDegree2Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block16Norm x).property (boundaryFullPowerDegree2Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block16Norm,boundaryFullPowerDegree2Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))))))=(boundaryFullPowerDegree2Block14Norm x).val+(boundaryFullPowerDegree2Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block14Norm x).property (boundaryFullPowerDegree2Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block14Norm,boundaryFullPowerDegree2Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x)))))))))+(((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x)))))))))+(((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x))))))))))=(boundaryFullPowerDegree2Block9Norm x).val+(boundaryFullPowerDegree2Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block9Norm x).property (boundaryFullPowerDegree2Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block9Norm,boundaryFullPowerDegree2Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x))=c} := by

  have he : ((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x))=(boundaryImPowerRow77_0Degree2Norm x).val+(boundaryImPowerRow77_1Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree2Norm x).property (boundaryImPowerRow77_1Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree2Norm,boundaryImPowerRow77_1Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x))=c} := by

  have he : ((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x))=(boundaryImPowerRow77_3Degree2Norm x).val+(boundaryImPowerRow77_4Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree2Norm x).property (boundaryImPowerRow77_4Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree2Norm,boundaryImPowerRow77_4Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x))))=(boundaryImPowerRow77_2Degree2Norm x).val+(boundaryFullPowerDegree2Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree2Norm x).property (boundaryFullPowerDegree2Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree2Norm,boundaryFullPowerDegree2Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x))))))=(boundaryFullPowerDegree2Block22Norm x).val+(boundaryFullPowerDegree2Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block22Norm x).property (boundaryFullPowerDegree2Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block22Norm,boundaryFullPowerDegree2Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x))=c} := by

  have he : ((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x))=(boundaryImPowerRow77_6Degree2Norm x).val+(boundaryImPowerRow77_7Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree2Norm x).property (boundaryImPowerRow77_7Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree2Norm,boundaryImPowerRow77_7Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x))))=(boundaryImPowerRow77_5Degree2Norm x).val+(boundaryFullPowerDegree2Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree2Norm x).property (boundaryFullPowerDegree2Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree2Norm,boundaryFullPowerDegree2Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))=c} := by

  have he : ((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))=(boundaryImPowerRow77_9Degree2Norm x).val+(boundaryImPowerRow77_10Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree2Norm x).property (boundaryImPowerRow77_10Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree2Norm,boundaryImPowerRow77_10Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))))=(boundaryImPowerRow77_8Degree2Norm x).val+(boundaryFullPowerDegree2Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree2Norm x).property (boundaryFullPowerDegree2Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree2Norm,boundaryFullPowerDegree2Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))))))=(boundaryFullPowerDegree2Block27Norm x).val+(boundaryFullPowerDegree2Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block27Norm x).property (boundaryFullPowerDegree2Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block27Norm,boundaryFullPowerDegree2Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x))))))))=(boundaryFullPowerDegree2Block25Norm x).val+(boundaryFullPowerDegree2Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block25Norm x).property (boundaryFullPowerDegree2Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block25Norm,boundaryFullPowerDegree2Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x))=c} := by

  have he : ((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x))=(boundaryImPowerRow77_12Degree2Norm x).val+(boundaryImPowerRow77_13Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree2Norm x).property (boundaryImPowerRow77_13Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree2Norm,boundaryImPowerRow77_13Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x))))=(boundaryImPowerRow77_11Degree2Norm x).val+(boundaryFullPowerDegree2Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree2Norm x).property (boundaryFullPowerDegree2Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree2Norm,boundaryFullPowerDegree2Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x))=c} := by

  have he : ((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x))=(boundaryImPowerRow77_15Degree2Norm x).val+(boundaryImPowerRow77_16Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree2Norm x).property (boundaryImPowerRow77_16Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree2Norm,boundaryImPowerRow77_16Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x))))=(boundaryImPowerRow77_14Degree2Norm x).val+(boundaryFullPowerDegree2Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree2Norm x).property (boundaryFullPowerDegree2Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree2Norm,boundaryFullPowerDegree2Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x))))))=(boundaryFullPowerDegree2Block33Norm x).val+(boundaryFullPowerDegree2Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block33Norm x).property (boundaryFullPowerDegree2Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block33Norm,boundaryFullPowerDegree2Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x))=c} := by

  have he : ((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x))=(boundaryImPowerRow77_18Degree2Norm x).val+(boundaryImPowerRow77_19Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree2Norm x).property (boundaryImPowerRow77_19Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree2Norm,boundaryImPowerRow77_19Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x))))=(boundaryImPowerRow77_17Degree2Norm x).val+(boundaryFullPowerDegree2Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree2Norm x).property (boundaryFullPowerDegree2Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree2Norm,boundaryFullPowerDegree2Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))=c} := by

  have he : ((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))=(boundaryImPowerRow77_21Degree2Norm x).val+(boundaryLowPowerRow77Degree2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree2Norm x).property (boundaryLowPowerRow77Degree2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree2Norm,boundaryLowPowerRow77Degree2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))=(boundaryImPowerRow77_20Degree2Norm x).val+(boundaryFullPowerDegree2Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree2Norm x).property (boundaryFullPowerDegree2Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree2Norm,boundaryFullPowerDegree2Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))=(boundaryFullPowerDegree2Block38Norm x).val+(boundaryFullPowerDegree2Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block38Norm x).property (boundaryFullPowerDegree2Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block38Norm,boundaryFullPowerDegree2Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))))=(boundaryFullPowerDegree2Block36Norm x).val+(boundaryFullPowerDegree2Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block36Norm x).property (boundaryFullPowerDegree2Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block36Norm,boundaryFullPowerDegree2Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x)))))))))+(((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x)))))))))+(((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))))))=(boundaryFullPowerDegree2Block31Norm x).val+(boundaryFullPowerDegree2Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block31Norm x).property (boundaryFullPowerDegree2Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block31Norm,boundaryFullPowerDegree2Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree2Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x)))))))))+(((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x)))))))))))+(((((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x)))))))))+(((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x)))))))))+(((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x)))))))))))+(((((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x)))))))))+(((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x))))))))))))=(boundaryFullPowerDegree2Block21Norm x).val+(boundaryFullPowerDegree2Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree2Block21Norm x).property (boundaryFullPowerDegree2Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block21Norm,boundaryFullPowerDegree2Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree2Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 2 x=c} := by

  have he0 : boundaryFullPowerRow77 2 x=((((((((((boundaryRePowerRow77_0 2 x)+(boundaryRePowerRow77_1 2 x)))+(((boundaryRePowerRow77_2 2 x)+(((boundaryRePowerRow77_3 2 x)+(boundaryRePowerRow77_4 2 x)))))))+(((((boundaryRePowerRow77_5 2 x)+(((boundaryRePowerRow77_6 2 x)+(boundaryRePowerRow77_7 2 x)))))+(((boundaryRePowerRow77_8 2 x)+(((boundaryRePowerRow77_9 2 x)+(boundaryRePowerRow77_10 2 x)))))))))+(((((((boundaryRePowerRow77_11 2 x)+(((boundaryRePowerRow77_12 2 x)+(boundaryRePowerRow77_13 2 x)))))+(((boundaryRePowerRow77_14 2 x)+(((boundaryRePowerRow77_15 2 x)+(boundaryRePowerRow77_16 2 x)))))))+(((((boundaryRePowerRow77_17 2 x)+(((boundaryRePowerRow77_18 2 x)+(boundaryRePowerRow77_19 2 x)))))+(((boundaryRePowerRow77_20 2 x)+(((boundaryRePowerRow77_21 2 x)+(boundaryRePowerRow77_22 2 x)))))))))))+(((((((((boundaryImPowerRow77_0 2 x)+(boundaryImPowerRow77_1 2 x)))+(((boundaryImPowerRow77_2 2 x)+(((boundaryImPowerRow77_3 2 x)+(boundaryImPowerRow77_4 2 x)))))))+(((((boundaryImPowerRow77_5 2 x)+(((boundaryImPowerRow77_6 2 x)+(boundaryImPowerRow77_7 2 x)))))+(((boundaryImPowerRow77_8 2 x)+(((boundaryImPowerRow77_9 2 x)+(boundaryImPowerRow77_10 2 x)))))))))+(((((((boundaryImPowerRow77_11 2 x)+(((boundaryImPowerRow77_12 2 x)+(boundaryImPowerRow77_13 2 x)))))+(((boundaryImPowerRow77_14 2 x)+(((boundaryImPowerRow77_15 2 x)+(boundaryImPowerRow77_16 2 x)))))))+(((((boundaryImPowerRow77_17 2 x)+(((boundaryImPowerRow77_18 2 x)+(boundaryImPowerRow77_19 2 x)))))+(((boundaryImPowerRow77_20 2 x)+(((boundaryImPowerRow77_21 2 x)+(boundaryLowPowerRow77 2 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree2Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree2Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
