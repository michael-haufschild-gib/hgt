import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree40Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree40Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x))=c} := by

  have he : ((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x))=(boundaryRePowerRow77_0Degree40Norm x).val+(boundaryRePowerRow77_1Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree40Norm x).property (boundaryRePowerRow77_1Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree40Norm,boundaryRePowerRow77_1Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x))=c} := by

  have he : ((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x))=(boundaryRePowerRow77_3Degree40Norm x).val+(boundaryRePowerRow77_4Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree40Norm x).property (boundaryRePowerRow77_4Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree40Norm,boundaryRePowerRow77_4Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x))))=(boundaryRePowerRow77_2Degree40Norm x).val+(boundaryFullPowerDegree40Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree40Norm x).property (boundaryFullPowerDegree40Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree40Norm,boundaryFullPowerDegree40Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x))))))=(boundaryFullPowerDegree40Block0Norm x).val+(boundaryFullPowerDegree40Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block0Norm x).property (boundaryFullPowerDegree40Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block0Norm,boundaryFullPowerDegree40Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x))=c} := by

  have he : ((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x))=(boundaryRePowerRow77_6Degree40Norm x).val+(boundaryRePowerRow77_7Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree40Norm x).property (boundaryRePowerRow77_7Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree40Norm,boundaryRePowerRow77_7Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x))))=(boundaryRePowerRow77_5Degree40Norm x).val+(boundaryFullPowerDegree40Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree40Norm x).property (boundaryFullPowerDegree40Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree40Norm,boundaryFullPowerDegree40Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))=c} := by

  have he : ((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))=(boundaryRePowerRow77_9Degree40Norm x).val+(boundaryRePowerRow77_10Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree40Norm x).property (boundaryRePowerRow77_10Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree40Norm,boundaryRePowerRow77_10Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))))=(boundaryRePowerRow77_8Degree40Norm x).val+(boundaryFullPowerDegree40Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree40Norm x).property (boundaryFullPowerDegree40Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree40Norm,boundaryFullPowerDegree40Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))))))=(boundaryFullPowerDegree40Block5Norm x).val+(boundaryFullPowerDegree40Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block5Norm x).property (boundaryFullPowerDegree40Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block5Norm,boundaryFullPowerDegree40Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x))))))))=(boundaryFullPowerDegree40Block3Norm x).val+(boundaryFullPowerDegree40Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block3Norm x).property (boundaryFullPowerDegree40Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block3Norm,boundaryFullPowerDegree40Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x))=c} := by

  have he : ((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x))=(boundaryRePowerRow77_12Degree40Norm x).val+(boundaryRePowerRow77_13Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree40Norm x).property (boundaryRePowerRow77_13Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree40Norm,boundaryRePowerRow77_13Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x))))=(boundaryRePowerRow77_11Degree40Norm x).val+(boundaryFullPowerDegree40Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree40Norm x).property (boundaryFullPowerDegree40Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree40Norm,boundaryFullPowerDegree40Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x))=c} := by

  have he : ((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x))=(boundaryRePowerRow77_15Degree40Norm x).val+(boundaryRePowerRow77_16Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree40Norm x).property (boundaryRePowerRow77_16Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree40Norm,boundaryRePowerRow77_16Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x))))=(boundaryRePowerRow77_14Degree40Norm x).val+(boundaryFullPowerDegree40Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree40Norm x).property (boundaryFullPowerDegree40Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree40Norm,boundaryFullPowerDegree40Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x))))))=(boundaryFullPowerDegree40Block11Norm x).val+(boundaryFullPowerDegree40Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block11Norm x).property (boundaryFullPowerDegree40Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block11Norm,boundaryFullPowerDegree40Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x))=c} := by

  have he : ((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x))=(boundaryRePowerRow77_18Degree40Norm x).val+(boundaryRePowerRow77_19Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree40Norm x).property (boundaryRePowerRow77_19Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree40Norm,boundaryRePowerRow77_19Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x))))=(boundaryRePowerRow77_17Degree40Norm x).val+(boundaryFullPowerDegree40Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree40Norm x).property (boundaryFullPowerDegree40Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree40Norm,boundaryFullPowerDegree40Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))=c} := by

  have he : ((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))=(boundaryRePowerRow77_21Degree40Norm x).val+(boundaryRePowerRow77_22Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree40Norm x).property (boundaryRePowerRow77_22Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree40Norm,boundaryRePowerRow77_22Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))=(boundaryRePowerRow77_20Degree40Norm x).val+(boundaryFullPowerDegree40Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree40Norm x).property (boundaryFullPowerDegree40Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree40Norm,boundaryFullPowerDegree40Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))))=(boundaryFullPowerDegree40Block16Norm x).val+(boundaryFullPowerDegree40Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block16Norm x).property (boundaryFullPowerDegree40Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block16Norm,boundaryFullPowerDegree40Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))))))=(boundaryFullPowerDegree40Block14Norm x).val+(boundaryFullPowerDegree40Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block14Norm x).property (boundaryFullPowerDegree40Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block14Norm,boundaryFullPowerDegree40Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x)))))))))+(((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x)))))))))+(((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x))))))))))=(boundaryFullPowerDegree40Block9Norm x).val+(boundaryFullPowerDegree40Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block9Norm x).property (boundaryFullPowerDegree40Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block9Norm,boundaryFullPowerDegree40Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x))=c} := by

  have he : ((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x))=(boundaryImPowerRow77_0Degree40Norm x).val+(boundaryImPowerRow77_1Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree40Norm x).property (boundaryImPowerRow77_1Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree40Norm,boundaryImPowerRow77_1Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x))=c} := by

  have he : ((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x))=(boundaryImPowerRow77_3Degree40Norm x).val+(boundaryImPowerRow77_4Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree40Norm x).property (boundaryImPowerRow77_4Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree40Norm,boundaryImPowerRow77_4Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x))))=(boundaryImPowerRow77_2Degree40Norm x).val+(boundaryFullPowerDegree40Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree40Norm x).property (boundaryFullPowerDegree40Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree40Norm,boundaryFullPowerDegree40Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x))))))=(boundaryFullPowerDegree40Block22Norm x).val+(boundaryFullPowerDegree40Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block22Norm x).property (boundaryFullPowerDegree40Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block22Norm,boundaryFullPowerDegree40Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x))=c} := by

  have he : ((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x))=(boundaryImPowerRow77_6Degree40Norm x).val+(boundaryImPowerRow77_7Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree40Norm x).property (boundaryImPowerRow77_7Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree40Norm,boundaryImPowerRow77_7Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x))))=(boundaryImPowerRow77_5Degree40Norm x).val+(boundaryFullPowerDegree40Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree40Norm x).property (boundaryFullPowerDegree40Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree40Norm,boundaryFullPowerDegree40Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))=c} := by

  have he : ((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))=(boundaryImPowerRow77_9Degree40Norm x).val+(boundaryImPowerRow77_10Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree40Norm x).property (boundaryImPowerRow77_10Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree40Norm,boundaryImPowerRow77_10Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))))=(boundaryImPowerRow77_8Degree40Norm x).val+(boundaryFullPowerDegree40Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree40Norm x).property (boundaryFullPowerDegree40Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree40Norm,boundaryFullPowerDegree40Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))))))=(boundaryFullPowerDegree40Block27Norm x).val+(boundaryFullPowerDegree40Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block27Norm x).property (boundaryFullPowerDegree40Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block27Norm,boundaryFullPowerDegree40Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x))))))))=(boundaryFullPowerDegree40Block25Norm x).val+(boundaryFullPowerDegree40Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block25Norm x).property (boundaryFullPowerDegree40Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block25Norm,boundaryFullPowerDegree40Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x))=c} := by

  have he : ((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x))=(boundaryImPowerRow77_12Degree40Norm x).val+(boundaryImPowerRow77_13Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree40Norm x).property (boundaryImPowerRow77_13Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree40Norm,boundaryImPowerRow77_13Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x))))=(boundaryImPowerRow77_11Degree40Norm x).val+(boundaryFullPowerDegree40Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree40Norm x).property (boundaryFullPowerDegree40Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree40Norm,boundaryFullPowerDegree40Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x))=c} := by

  have he : ((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x))=(boundaryImPowerRow77_15Degree40Norm x).val+(boundaryImPowerRow77_16Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree40Norm x).property (boundaryImPowerRow77_16Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree40Norm,boundaryImPowerRow77_16Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x))))=(boundaryImPowerRow77_14Degree40Norm x).val+(boundaryFullPowerDegree40Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree40Norm x).property (boundaryFullPowerDegree40Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree40Norm,boundaryFullPowerDegree40Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x))))))=(boundaryFullPowerDegree40Block33Norm x).val+(boundaryFullPowerDegree40Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block33Norm x).property (boundaryFullPowerDegree40Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block33Norm,boundaryFullPowerDegree40Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x))=c} := by

  have he : ((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x))=(boundaryImPowerRow77_18Degree40Norm x).val+(boundaryImPowerRow77_19Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree40Norm x).property (boundaryImPowerRow77_19Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree40Norm,boundaryImPowerRow77_19Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x))))=(boundaryImPowerRow77_17Degree40Norm x).val+(boundaryFullPowerDegree40Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree40Norm x).property (boundaryFullPowerDegree40Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree40Norm,boundaryFullPowerDegree40Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))=c} := by

  have he : ((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))=(boundaryImPowerRow77_21Degree40Norm x).val+(boundaryLowPowerRow77Degree40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree40Norm x).property (boundaryLowPowerRow77Degree40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree40Norm,boundaryLowPowerRow77Degree40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))=(boundaryImPowerRow77_20Degree40Norm x).val+(boundaryFullPowerDegree40Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree40Norm x).property (boundaryFullPowerDegree40Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree40Norm,boundaryFullPowerDegree40Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))=(boundaryFullPowerDegree40Block38Norm x).val+(boundaryFullPowerDegree40Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block38Norm x).property (boundaryFullPowerDegree40Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block38Norm,boundaryFullPowerDegree40Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))))=(boundaryFullPowerDegree40Block36Norm x).val+(boundaryFullPowerDegree40Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block36Norm x).property (boundaryFullPowerDegree40Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block36Norm,boundaryFullPowerDegree40Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x)))))))))+(((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x)))))))))+(((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))))))=(boundaryFullPowerDegree40Block31Norm x).val+(boundaryFullPowerDegree40Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block31Norm x).property (boundaryFullPowerDegree40Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block31Norm,boundaryFullPowerDegree40Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree40Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x)))))))))+(((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x)))))))))))+(((((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x)))))))))+(((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x)))))))))+(((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x)))))))))))+(((((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x)))))))))+(((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x))))))))))))=(boundaryFullPowerDegree40Block21Norm x).val+(boundaryFullPowerDegree40Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree40Block21Norm x).property (boundaryFullPowerDegree40Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block21Norm,boundaryFullPowerDegree40Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree40Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 40 x=c} := by

  have he0 : boundaryFullPowerRow77 40 x=((((((((((boundaryRePowerRow77_0 40 x)+(boundaryRePowerRow77_1 40 x)))+(((boundaryRePowerRow77_2 40 x)+(((boundaryRePowerRow77_3 40 x)+(boundaryRePowerRow77_4 40 x)))))))+(((((boundaryRePowerRow77_5 40 x)+(((boundaryRePowerRow77_6 40 x)+(boundaryRePowerRow77_7 40 x)))))+(((boundaryRePowerRow77_8 40 x)+(((boundaryRePowerRow77_9 40 x)+(boundaryRePowerRow77_10 40 x)))))))))+(((((((boundaryRePowerRow77_11 40 x)+(((boundaryRePowerRow77_12 40 x)+(boundaryRePowerRow77_13 40 x)))))+(((boundaryRePowerRow77_14 40 x)+(((boundaryRePowerRow77_15 40 x)+(boundaryRePowerRow77_16 40 x)))))))+(((((boundaryRePowerRow77_17 40 x)+(((boundaryRePowerRow77_18 40 x)+(boundaryRePowerRow77_19 40 x)))))+(((boundaryRePowerRow77_20 40 x)+(((boundaryRePowerRow77_21 40 x)+(boundaryRePowerRow77_22 40 x)))))))))))+(((((((((boundaryImPowerRow77_0 40 x)+(boundaryImPowerRow77_1 40 x)))+(((boundaryImPowerRow77_2 40 x)+(((boundaryImPowerRow77_3 40 x)+(boundaryImPowerRow77_4 40 x)))))))+(((((boundaryImPowerRow77_5 40 x)+(((boundaryImPowerRow77_6 40 x)+(boundaryImPowerRow77_7 40 x)))))+(((boundaryImPowerRow77_8 40 x)+(((boundaryImPowerRow77_9 40 x)+(boundaryImPowerRow77_10 40 x)))))))))+(((((((boundaryImPowerRow77_11 40 x)+(((boundaryImPowerRow77_12 40 x)+(boundaryImPowerRow77_13 40 x)))))+(((boundaryImPowerRow77_14 40 x)+(((boundaryImPowerRow77_15 40 x)+(boundaryImPowerRow77_16 40 x)))))))+(((((boundaryImPowerRow77_17 40 x)+(((boundaryImPowerRow77_18 40 x)+(boundaryImPowerRow77_19 40 x)))))+(((boundaryImPowerRow77_20 40 x)+(((boundaryImPowerRow77_21 40 x)+(boundaryLowPowerRow77 40 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree40Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree40Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
