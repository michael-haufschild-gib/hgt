import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree13Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree13Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x))=c} := by

  have he : ((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x))=(boundaryRePowerRow77_0Degree13Norm x).val+(boundaryRePowerRow77_1Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree13Norm x).property (boundaryRePowerRow77_1Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree13Norm,boundaryRePowerRow77_1Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x))=c} := by

  have he : ((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x))=(boundaryRePowerRow77_3Degree13Norm x).val+(boundaryRePowerRow77_4Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree13Norm x).property (boundaryRePowerRow77_4Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree13Norm,boundaryRePowerRow77_4Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x))))=(boundaryRePowerRow77_2Degree13Norm x).val+(boundaryFullPowerDegree13Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree13Norm x).property (boundaryFullPowerDegree13Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree13Norm,boundaryFullPowerDegree13Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x))))))=(boundaryFullPowerDegree13Block0Norm x).val+(boundaryFullPowerDegree13Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block0Norm x).property (boundaryFullPowerDegree13Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block0Norm,boundaryFullPowerDegree13Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x))=c} := by

  have he : ((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x))=(boundaryRePowerRow77_6Degree13Norm x).val+(boundaryRePowerRow77_7Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree13Norm x).property (boundaryRePowerRow77_7Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree13Norm,boundaryRePowerRow77_7Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x))))=(boundaryRePowerRow77_5Degree13Norm x).val+(boundaryFullPowerDegree13Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree13Norm x).property (boundaryFullPowerDegree13Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree13Norm,boundaryFullPowerDegree13Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))=c} := by

  have he : ((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))=(boundaryRePowerRow77_9Degree13Norm x).val+(boundaryRePowerRow77_10Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree13Norm x).property (boundaryRePowerRow77_10Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree13Norm,boundaryRePowerRow77_10Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))))=(boundaryRePowerRow77_8Degree13Norm x).val+(boundaryFullPowerDegree13Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree13Norm x).property (boundaryFullPowerDegree13Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree13Norm,boundaryFullPowerDegree13Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))))))=(boundaryFullPowerDegree13Block5Norm x).val+(boundaryFullPowerDegree13Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block5Norm x).property (boundaryFullPowerDegree13Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block5Norm,boundaryFullPowerDegree13Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x))))))))=(boundaryFullPowerDegree13Block3Norm x).val+(boundaryFullPowerDegree13Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block3Norm x).property (boundaryFullPowerDegree13Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block3Norm,boundaryFullPowerDegree13Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x))=c} := by

  have he : ((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x))=(boundaryRePowerRow77_12Degree13Norm x).val+(boundaryRePowerRow77_13Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree13Norm x).property (boundaryRePowerRow77_13Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree13Norm,boundaryRePowerRow77_13Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x))))=(boundaryRePowerRow77_11Degree13Norm x).val+(boundaryFullPowerDegree13Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree13Norm x).property (boundaryFullPowerDegree13Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree13Norm,boundaryFullPowerDegree13Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x))=c} := by

  have he : ((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x))=(boundaryRePowerRow77_15Degree13Norm x).val+(boundaryRePowerRow77_16Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree13Norm x).property (boundaryRePowerRow77_16Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree13Norm,boundaryRePowerRow77_16Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x))))=(boundaryRePowerRow77_14Degree13Norm x).val+(boundaryFullPowerDegree13Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree13Norm x).property (boundaryFullPowerDegree13Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree13Norm,boundaryFullPowerDegree13Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x))))))=(boundaryFullPowerDegree13Block11Norm x).val+(boundaryFullPowerDegree13Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block11Norm x).property (boundaryFullPowerDegree13Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block11Norm,boundaryFullPowerDegree13Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x))=c} := by

  have he : ((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x))=(boundaryRePowerRow77_18Degree13Norm x).val+(boundaryRePowerRow77_19Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree13Norm x).property (boundaryRePowerRow77_19Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree13Norm,boundaryRePowerRow77_19Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x))))=(boundaryRePowerRow77_17Degree13Norm x).val+(boundaryFullPowerDegree13Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree13Norm x).property (boundaryFullPowerDegree13Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree13Norm,boundaryFullPowerDegree13Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))=c} := by

  have he : ((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))=(boundaryRePowerRow77_21Degree13Norm x).val+(boundaryRePowerRow77_22Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree13Norm x).property (boundaryRePowerRow77_22Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree13Norm,boundaryRePowerRow77_22Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))=(boundaryRePowerRow77_20Degree13Norm x).val+(boundaryFullPowerDegree13Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree13Norm x).property (boundaryFullPowerDegree13Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree13Norm,boundaryFullPowerDegree13Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))))=(boundaryFullPowerDegree13Block16Norm x).val+(boundaryFullPowerDegree13Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block16Norm x).property (boundaryFullPowerDegree13Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block16Norm,boundaryFullPowerDegree13Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))))))=(boundaryFullPowerDegree13Block14Norm x).val+(boundaryFullPowerDegree13Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block14Norm x).property (boundaryFullPowerDegree13Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block14Norm,boundaryFullPowerDegree13Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x)))))))))+(((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x)))))))))+(((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x))))))))))=(boundaryFullPowerDegree13Block9Norm x).val+(boundaryFullPowerDegree13Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block9Norm x).property (boundaryFullPowerDegree13Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block9Norm,boundaryFullPowerDegree13Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x))=c} := by

  have he : ((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x))=(boundaryImPowerRow77_0Degree13Norm x).val+(boundaryImPowerRow77_1Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree13Norm x).property (boundaryImPowerRow77_1Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree13Norm,boundaryImPowerRow77_1Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x))=c} := by

  have he : ((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x))=(boundaryImPowerRow77_3Degree13Norm x).val+(boundaryImPowerRow77_4Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree13Norm x).property (boundaryImPowerRow77_4Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree13Norm,boundaryImPowerRow77_4Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x))))=(boundaryImPowerRow77_2Degree13Norm x).val+(boundaryFullPowerDegree13Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree13Norm x).property (boundaryFullPowerDegree13Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree13Norm,boundaryFullPowerDegree13Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x))))))=(boundaryFullPowerDegree13Block22Norm x).val+(boundaryFullPowerDegree13Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block22Norm x).property (boundaryFullPowerDegree13Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block22Norm,boundaryFullPowerDegree13Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x))=c} := by

  have he : ((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x))=(boundaryImPowerRow77_6Degree13Norm x).val+(boundaryImPowerRow77_7Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree13Norm x).property (boundaryImPowerRow77_7Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree13Norm,boundaryImPowerRow77_7Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x))))=(boundaryImPowerRow77_5Degree13Norm x).val+(boundaryFullPowerDegree13Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree13Norm x).property (boundaryFullPowerDegree13Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree13Norm,boundaryFullPowerDegree13Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))=c} := by

  have he : ((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))=(boundaryImPowerRow77_9Degree13Norm x).val+(boundaryImPowerRow77_10Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree13Norm x).property (boundaryImPowerRow77_10Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree13Norm,boundaryImPowerRow77_10Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))))=(boundaryImPowerRow77_8Degree13Norm x).val+(boundaryFullPowerDegree13Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree13Norm x).property (boundaryFullPowerDegree13Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree13Norm,boundaryFullPowerDegree13Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))))))=(boundaryFullPowerDegree13Block27Norm x).val+(boundaryFullPowerDegree13Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block27Norm x).property (boundaryFullPowerDegree13Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block27Norm,boundaryFullPowerDegree13Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x))))))))=(boundaryFullPowerDegree13Block25Norm x).val+(boundaryFullPowerDegree13Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block25Norm x).property (boundaryFullPowerDegree13Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block25Norm,boundaryFullPowerDegree13Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x))=c} := by

  have he : ((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x))=(boundaryImPowerRow77_12Degree13Norm x).val+(boundaryImPowerRow77_13Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree13Norm x).property (boundaryImPowerRow77_13Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree13Norm,boundaryImPowerRow77_13Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x))))=(boundaryImPowerRow77_11Degree13Norm x).val+(boundaryFullPowerDegree13Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree13Norm x).property (boundaryFullPowerDegree13Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree13Norm,boundaryFullPowerDegree13Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x))=c} := by

  have he : ((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x))=(boundaryImPowerRow77_15Degree13Norm x).val+(boundaryImPowerRow77_16Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree13Norm x).property (boundaryImPowerRow77_16Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree13Norm,boundaryImPowerRow77_16Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x))))=(boundaryImPowerRow77_14Degree13Norm x).val+(boundaryFullPowerDegree13Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree13Norm x).property (boundaryFullPowerDegree13Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree13Norm,boundaryFullPowerDegree13Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x))))))=(boundaryFullPowerDegree13Block33Norm x).val+(boundaryFullPowerDegree13Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block33Norm x).property (boundaryFullPowerDegree13Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block33Norm,boundaryFullPowerDegree13Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x))=c} := by

  have he : ((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x))=(boundaryImPowerRow77_18Degree13Norm x).val+(boundaryImPowerRow77_19Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree13Norm x).property (boundaryImPowerRow77_19Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree13Norm,boundaryImPowerRow77_19Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x))))=(boundaryImPowerRow77_17Degree13Norm x).val+(boundaryFullPowerDegree13Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree13Norm x).property (boundaryFullPowerDegree13Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree13Norm,boundaryFullPowerDegree13Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))=c} := by

  have he : ((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))=(boundaryImPowerRow77_21Degree13Norm x).val+(boundaryLowPowerRow77Degree13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree13Norm x).property (boundaryLowPowerRow77Degree13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree13Norm,boundaryLowPowerRow77Degree13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))=(boundaryImPowerRow77_20Degree13Norm x).val+(boundaryFullPowerDegree13Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree13Norm x).property (boundaryFullPowerDegree13Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree13Norm,boundaryFullPowerDegree13Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))=(boundaryFullPowerDegree13Block38Norm x).val+(boundaryFullPowerDegree13Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block38Norm x).property (boundaryFullPowerDegree13Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block38Norm,boundaryFullPowerDegree13Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))))=(boundaryFullPowerDegree13Block36Norm x).val+(boundaryFullPowerDegree13Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block36Norm x).property (boundaryFullPowerDegree13Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block36Norm,boundaryFullPowerDegree13Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x)))))))))+(((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x)))))))))+(((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))))))=(boundaryFullPowerDegree13Block31Norm x).val+(boundaryFullPowerDegree13Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block31Norm x).property (boundaryFullPowerDegree13Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block31Norm,boundaryFullPowerDegree13Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree13Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x)))))))))+(((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x)))))))))))+(((((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x)))))))))+(((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x)))))))))+(((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x)))))))))))+(((((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x)))))))))+(((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x))))))))))))=(boundaryFullPowerDegree13Block21Norm x).val+(boundaryFullPowerDegree13Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree13Block21Norm x).property (boundaryFullPowerDegree13Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block21Norm,boundaryFullPowerDegree13Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree13Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 13 x=c} := by

  have he0 : boundaryFullPowerRow77 13 x=((((((((((boundaryRePowerRow77_0 13 x)+(boundaryRePowerRow77_1 13 x)))+(((boundaryRePowerRow77_2 13 x)+(((boundaryRePowerRow77_3 13 x)+(boundaryRePowerRow77_4 13 x)))))))+(((((boundaryRePowerRow77_5 13 x)+(((boundaryRePowerRow77_6 13 x)+(boundaryRePowerRow77_7 13 x)))))+(((boundaryRePowerRow77_8 13 x)+(((boundaryRePowerRow77_9 13 x)+(boundaryRePowerRow77_10 13 x)))))))))+(((((((boundaryRePowerRow77_11 13 x)+(((boundaryRePowerRow77_12 13 x)+(boundaryRePowerRow77_13 13 x)))))+(((boundaryRePowerRow77_14 13 x)+(((boundaryRePowerRow77_15 13 x)+(boundaryRePowerRow77_16 13 x)))))))+(((((boundaryRePowerRow77_17 13 x)+(((boundaryRePowerRow77_18 13 x)+(boundaryRePowerRow77_19 13 x)))))+(((boundaryRePowerRow77_20 13 x)+(((boundaryRePowerRow77_21 13 x)+(boundaryRePowerRow77_22 13 x)))))))))))+(((((((((boundaryImPowerRow77_0 13 x)+(boundaryImPowerRow77_1 13 x)))+(((boundaryImPowerRow77_2 13 x)+(((boundaryImPowerRow77_3 13 x)+(boundaryImPowerRow77_4 13 x)))))))+(((((boundaryImPowerRow77_5 13 x)+(((boundaryImPowerRow77_6 13 x)+(boundaryImPowerRow77_7 13 x)))))+(((boundaryImPowerRow77_8 13 x)+(((boundaryImPowerRow77_9 13 x)+(boundaryImPowerRow77_10 13 x)))))))))+(((((((boundaryImPowerRow77_11 13 x)+(((boundaryImPowerRow77_12 13 x)+(boundaryImPowerRow77_13 13 x)))))+(((boundaryImPowerRow77_14 13 x)+(((boundaryImPowerRow77_15 13 x)+(boundaryImPowerRow77_16 13 x)))))))+(((((boundaryImPowerRow77_17 13 x)+(((boundaryImPowerRow77_18 13 x)+(boundaryImPowerRow77_19 13 x)))))+(((boundaryImPowerRow77_20 13 x)+(((boundaryImPowerRow77_21 13 x)+(boundaryLowPowerRow77 13 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree13Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree13Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
