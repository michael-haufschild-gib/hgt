import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree57Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree57Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x))=c} := by

  have he : ((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x))=(boundaryRePowerRow77_0Degree57Norm x).val+(boundaryRePowerRow77_1Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree57Norm x).property (boundaryRePowerRow77_1Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree57Norm,boundaryRePowerRow77_1Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x))=c} := by

  have he : ((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x))=(boundaryRePowerRow77_3Degree57Norm x).val+(boundaryRePowerRow77_4Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree57Norm x).property (boundaryRePowerRow77_4Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree57Norm,boundaryRePowerRow77_4Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x))))=(boundaryRePowerRow77_2Degree57Norm x).val+(boundaryFullPowerDegree57Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree57Norm x).property (boundaryFullPowerDegree57Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree57Norm,boundaryFullPowerDegree57Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x))))))=(boundaryFullPowerDegree57Block0Norm x).val+(boundaryFullPowerDegree57Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block0Norm x).property (boundaryFullPowerDegree57Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block0Norm,boundaryFullPowerDegree57Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x))=c} := by

  have he : ((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x))=(boundaryRePowerRow77_6Degree57Norm x).val+(boundaryRePowerRow77_7Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree57Norm x).property (boundaryRePowerRow77_7Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree57Norm,boundaryRePowerRow77_7Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x))))=(boundaryRePowerRow77_5Degree57Norm x).val+(boundaryFullPowerDegree57Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree57Norm x).property (boundaryFullPowerDegree57Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree57Norm,boundaryFullPowerDegree57Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))=c} := by

  have he : ((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))=(boundaryRePowerRow77_9Degree57Norm x).val+(boundaryRePowerRow77_10Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree57Norm x).property (boundaryRePowerRow77_10Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree57Norm,boundaryRePowerRow77_10Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))))=(boundaryRePowerRow77_8Degree57Norm x).val+(boundaryFullPowerDegree57Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree57Norm x).property (boundaryFullPowerDegree57Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree57Norm,boundaryFullPowerDegree57Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))))))=(boundaryFullPowerDegree57Block5Norm x).val+(boundaryFullPowerDegree57Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block5Norm x).property (boundaryFullPowerDegree57Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block5Norm,boundaryFullPowerDegree57Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x))))))))=(boundaryFullPowerDegree57Block3Norm x).val+(boundaryFullPowerDegree57Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block3Norm x).property (boundaryFullPowerDegree57Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block3Norm,boundaryFullPowerDegree57Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x))=c} := by

  have he : ((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x))=(boundaryRePowerRow77_12Degree57Norm x).val+(boundaryRePowerRow77_13Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree57Norm x).property (boundaryRePowerRow77_13Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree57Norm,boundaryRePowerRow77_13Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x))))=(boundaryRePowerRow77_11Degree57Norm x).val+(boundaryFullPowerDegree57Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree57Norm x).property (boundaryFullPowerDegree57Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree57Norm,boundaryFullPowerDegree57Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x))=c} := by

  have he : ((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x))=(boundaryRePowerRow77_15Degree57Norm x).val+(boundaryRePowerRow77_16Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree57Norm x).property (boundaryRePowerRow77_16Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree57Norm,boundaryRePowerRow77_16Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x))))=(boundaryRePowerRow77_14Degree57Norm x).val+(boundaryFullPowerDegree57Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree57Norm x).property (boundaryFullPowerDegree57Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree57Norm,boundaryFullPowerDegree57Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x))))))=(boundaryFullPowerDegree57Block11Norm x).val+(boundaryFullPowerDegree57Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block11Norm x).property (boundaryFullPowerDegree57Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block11Norm,boundaryFullPowerDegree57Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x))=c} := by

  have he : ((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x))=(boundaryRePowerRow77_18Degree57Norm x).val+(boundaryRePowerRow77_19Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree57Norm x).property (boundaryRePowerRow77_19Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree57Norm,boundaryRePowerRow77_19Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x))))=(boundaryRePowerRow77_17Degree57Norm x).val+(boundaryFullPowerDegree57Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree57Norm x).property (boundaryFullPowerDegree57Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree57Norm,boundaryFullPowerDegree57Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))=c} := by

  have he : ((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))=(boundaryRePowerRow77_21Degree57Norm x).val+(boundaryRePowerRow77_22Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree57Norm x).property (boundaryRePowerRow77_22Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree57Norm,boundaryRePowerRow77_22Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))=(boundaryRePowerRow77_20Degree57Norm x).val+(boundaryFullPowerDegree57Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree57Norm x).property (boundaryFullPowerDegree57Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree57Norm,boundaryFullPowerDegree57Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))))=(boundaryFullPowerDegree57Block16Norm x).val+(boundaryFullPowerDegree57Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block16Norm x).property (boundaryFullPowerDegree57Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block16Norm,boundaryFullPowerDegree57Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))))))=(boundaryFullPowerDegree57Block14Norm x).val+(boundaryFullPowerDegree57Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block14Norm x).property (boundaryFullPowerDegree57Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block14Norm,boundaryFullPowerDegree57Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x)))))))))+(((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x)))))))))+(((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x))))))))))=(boundaryFullPowerDegree57Block9Norm x).val+(boundaryFullPowerDegree57Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block9Norm x).property (boundaryFullPowerDegree57Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block9Norm,boundaryFullPowerDegree57Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x))=c} := by

  have he : ((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x))=(boundaryImPowerRow77_0Degree57Norm x).val+(boundaryImPowerRow77_1Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree57Norm x).property (boundaryImPowerRow77_1Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree57Norm,boundaryImPowerRow77_1Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x))=c} := by

  have he : ((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x))=(boundaryImPowerRow77_3Degree57Norm x).val+(boundaryImPowerRow77_4Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree57Norm x).property (boundaryImPowerRow77_4Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree57Norm,boundaryImPowerRow77_4Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x))))=(boundaryImPowerRow77_2Degree57Norm x).val+(boundaryFullPowerDegree57Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree57Norm x).property (boundaryFullPowerDegree57Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree57Norm,boundaryFullPowerDegree57Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x))))))=(boundaryFullPowerDegree57Block22Norm x).val+(boundaryFullPowerDegree57Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block22Norm x).property (boundaryFullPowerDegree57Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block22Norm,boundaryFullPowerDegree57Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x))=c} := by

  have he : ((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x))=(boundaryImPowerRow77_6Degree57Norm x).val+(boundaryImPowerRow77_7Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree57Norm x).property (boundaryImPowerRow77_7Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree57Norm,boundaryImPowerRow77_7Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x))))=(boundaryImPowerRow77_5Degree57Norm x).val+(boundaryFullPowerDegree57Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree57Norm x).property (boundaryFullPowerDegree57Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree57Norm,boundaryFullPowerDegree57Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))=c} := by

  have he : ((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))=(boundaryImPowerRow77_9Degree57Norm x).val+(boundaryImPowerRow77_10Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree57Norm x).property (boundaryImPowerRow77_10Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree57Norm,boundaryImPowerRow77_10Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))))=(boundaryImPowerRow77_8Degree57Norm x).val+(boundaryFullPowerDegree57Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree57Norm x).property (boundaryFullPowerDegree57Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree57Norm,boundaryFullPowerDegree57Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))))))=(boundaryFullPowerDegree57Block27Norm x).val+(boundaryFullPowerDegree57Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block27Norm x).property (boundaryFullPowerDegree57Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block27Norm,boundaryFullPowerDegree57Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x))))))))=(boundaryFullPowerDegree57Block25Norm x).val+(boundaryFullPowerDegree57Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block25Norm x).property (boundaryFullPowerDegree57Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block25Norm,boundaryFullPowerDegree57Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x))=c} := by

  have he : ((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x))=(boundaryImPowerRow77_12Degree57Norm x).val+(boundaryImPowerRow77_13Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree57Norm x).property (boundaryImPowerRow77_13Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree57Norm,boundaryImPowerRow77_13Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x))))=(boundaryImPowerRow77_11Degree57Norm x).val+(boundaryFullPowerDegree57Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree57Norm x).property (boundaryFullPowerDegree57Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree57Norm,boundaryFullPowerDegree57Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x))=c} := by

  have he : ((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x))=(boundaryImPowerRow77_15Degree57Norm x).val+(boundaryImPowerRow77_16Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree57Norm x).property (boundaryImPowerRow77_16Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree57Norm,boundaryImPowerRow77_16Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x))))=(boundaryImPowerRow77_14Degree57Norm x).val+(boundaryFullPowerDegree57Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree57Norm x).property (boundaryFullPowerDegree57Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree57Norm,boundaryFullPowerDegree57Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x))))))=(boundaryFullPowerDegree57Block33Norm x).val+(boundaryFullPowerDegree57Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block33Norm x).property (boundaryFullPowerDegree57Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block33Norm,boundaryFullPowerDegree57Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x))=c} := by

  have he : ((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x))=(boundaryImPowerRow77_18Degree57Norm x).val+(boundaryImPowerRow77_19Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree57Norm x).property (boundaryImPowerRow77_19Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree57Norm,boundaryImPowerRow77_19Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x))))=(boundaryImPowerRow77_17Degree57Norm x).val+(boundaryFullPowerDegree57Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree57Norm x).property (boundaryFullPowerDegree57Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree57Norm,boundaryFullPowerDegree57Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))=c} := by

  have he : ((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))=(boundaryImPowerRow77_21Degree57Norm x).val+(boundaryLowPowerRow77Degree57Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree57Norm x).property (boundaryLowPowerRow77Degree57Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree57Norm,boundaryLowPowerRow77Degree57Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))=(boundaryImPowerRow77_20Degree57Norm x).val+(boundaryFullPowerDegree57Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree57Norm x).property (boundaryFullPowerDegree57Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree57Norm,boundaryFullPowerDegree57Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))=(boundaryFullPowerDegree57Block38Norm x).val+(boundaryFullPowerDegree57Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block38Norm x).property (boundaryFullPowerDegree57Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block38Norm,boundaryFullPowerDegree57Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))))=(boundaryFullPowerDegree57Block36Norm x).val+(boundaryFullPowerDegree57Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block36Norm x).property (boundaryFullPowerDegree57Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block36Norm,boundaryFullPowerDegree57Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x)))))))))+(((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x)))))))))+(((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))))))=(boundaryFullPowerDegree57Block31Norm x).val+(boundaryFullPowerDegree57Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block31Norm x).property (boundaryFullPowerDegree57Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block31Norm,boundaryFullPowerDegree57Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree57Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x)))))))))+(((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x)))))))))))+(((((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x)))))))))+(((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x)))))))))+(((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x)))))))))))+(((((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x)))))))))+(((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x))))))))))))=(boundaryFullPowerDegree57Block21Norm x).val+(boundaryFullPowerDegree57Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree57Block21Norm x).property (boundaryFullPowerDegree57Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block21Norm,boundaryFullPowerDegree57Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree57Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 57 x=c} := by

  have he0 : boundaryFullPowerRow77 57 x=((((((((((boundaryRePowerRow77_0 57 x)+(boundaryRePowerRow77_1 57 x)))+(((boundaryRePowerRow77_2 57 x)+(((boundaryRePowerRow77_3 57 x)+(boundaryRePowerRow77_4 57 x)))))))+(((((boundaryRePowerRow77_5 57 x)+(((boundaryRePowerRow77_6 57 x)+(boundaryRePowerRow77_7 57 x)))))+(((boundaryRePowerRow77_8 57 x)+(((boundaryRePowerRow77_9 57 x)+(boundaryRePowerRow77_10 57 x)))))))))+(((((((boundaryRePowerRow77_11 57 x)+(((boundaryRePowerRow77_12 57 x)+(boundaryRePowerRow77_13 57 x)))))+(((boundaryRePowerRow77_14 57 x)+(((boundaryRePowerRow77_15 57 x)+(boundaryRePowerRow77_16 57 x)))))))+(((((boundaryRePowerRow77_17 57 x)+(((boundaryRePowerRow77_18 57 x)+(boundaryRePowerRow77_19 57 x)))))+(((boundaryRePowerRow77_20 57 x)+(((boundaryRePowerRow77_21 57 x)+(boundaryRePowerRow77_22 57 x)))))))))))+(((((((((boundaryImPowerRow77_0 57 x)+(boundaryImPowerRow77_1 57 x)))+(((boundaryImPowerRow77_2 57 x)+(((boundaryImPowerRow77_3 57 x)+(boundaryImPowerRow77_4 57 x)))))))+(((((boundaryImPowerRow77_5 57 x)+(((boundaryImPowerRow77_6 57 x)+(boundaryImPowerRow77_7 57 x)))))+(((boundaryImPowerRow77_8 57 x)+(((boundaryImPowerRow77_9 57 x)+(boundaryImPowerRow77_10 57 x)))))))))+(((((((boundaryImPowerRow77_11 57 x)+(((boundaryImPowerRow77_12 57 x)+(boundaryImPowerRow77_13 57 x)))))+(((boundaryImPowerRow77_14 57 x)+(((boundaryImPowerRow77_15 57 x)+(boundaryImPowerRow77_16 57 x)))))))+(((((boundaryImPowerRow77_17 57 x)+(((boundaryImPowerRow77_18 57 x)+(boundaryImPowerRow77_19 57 x)))))+(((boundaryImPowerRow77_20 57 x)+(((boundaryImPowerRow77_21 57 x)+(boundaryLowPowerRow77 57 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree57Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree57Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
