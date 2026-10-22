import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree52Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree52Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x))=c} := by

  have he : ((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x))=(boundaryRePowerRow77_0Degree52Norm x).val+(boundaryRePowerRow77_1Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree52Norm x).property (boundaryRePowerRow77_1Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree52Norm,boundaryRePowerRow77_1Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x))=c} := by

  have he : ((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x))=(boundaryRePowerRow77_3Degree52Norm x).val+(boundaryRePowerRow77_4Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree52Norm x).property (boundaryRePowerRow77_4Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree52Norm,boundaryRePowerRow77_4Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x))))=(boundaryRePowerRow77_2Degree52Norm x).val+(boundaryFullPowerDegree52Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree52Norm x).property (boundaryFullPowerDegree52Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree52Norm,boundaryFullPowerDegree52Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x))))))=(boundaryFullPowerDegree52Block0Norm x).val+(boundaryFullPowerDegree52Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block0Norm x).property (boundaryFullPowerDegree52Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block0Norm,boundaryFullPowerDegree52Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x))=c} := by

  have he : ((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x))=(boundaryRePowerRow77_6Degree52Norm x).val+(boundaryRePowerRow77_7Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree52Norm x).property (boundaryRePowerRow77_7Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree52Norm,boundaryRePowerRow77_7Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x))))=(boundaryRePowerRow77_5Degree52Norm x).val+(boundaryFullPowerDegree52Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree52Norm x).property (boundaryFullPowerDegree52Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree52Norm,boundaryFullPowerDegree52Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))=c} := by

  have he : ((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))=(boundaryRePowerRow77_9Degree52Norm x).val+(boundaryRePowerRow77_10Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree52Norm x).property (boundaryRePowerRow77_10Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree52Norm,boundaryRePowerRow77_10Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))))=(boundaryRePowerRow77_8Degree52Norm x).val+(boundaryFullPowerDegree52Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree52Norm x).property (boundaryFullPowerDegree52Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree52Norm,boundaryFullPowerDegree52Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))))))=(boundaryFullPowerDegree52Block5Norm x).val+(boundaryFullPowerDegree52Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block5Norm x).property (boundaryFullPowerDegree52Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block5Norm,boundaryFullPowerDegree52Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x))))))))=(boundaryFullPowerDegree52Block3Norm x).val+(boundaryFullPowerDegree52Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block3Norm x).property (boundaryFullPowerDegree52Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block3Norm,boundaryFullPowerDegree52Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x))=c} := by

  have he : ((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x))=(boundaryRePowerRow77_12Degree52Norm x).val+(boundaryRePowerRow77_13Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree52Norm x).property (boundaryRePowerRow77_13Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree52Norm,boundaryRePowerRow77_13Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x))))=(boundaryRePowerRow77_11Degree52Norm x).val+(boundaryFullPowerDegree52Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree52Norm x).property (boundaryFullPowerDegree52Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree52Norm,boundaryFullPowerDegree52Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x))=c} := by

  have he : ((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x))=(boundaryRePowerRow77_15Degree52Norm x).val+(boundaryRePowerRow77_16Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree52Norm x).property (boundaryRePowerRow77_16Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree52Norm,boundaryRePowerRow77_16Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x))))=(boundaryRePowerRow77_14Degree52Norm x).val+(boundaryFullPowerDegree52Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree52Norm x).property (boundaryFullPowerDegree52Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree52Norm,boundaryFullPowerDegree52Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x))))))=(boundaryFullPowerDegree52Block11Norm x).val+(boundaryFullPowerDegree52Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block11Norm x).property (boundaryFullPowerDegree52Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block11Norm,boundaryFullPowerDegree52Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x))=c} := by

  have he : ((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x))=(boundaryRePowerRow77_18Degree52Norm x).val+(boundaryRePowerRow77_19Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree52Norm x).property (boundaryRePowerRow77_19Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree52Norm,boundaryRePowerRow77_19Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x))))=(boundaryRePowerRow77_17Degree52Norm x).val+(boundaryFullPowerDegree52Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree52Norm x).property (boundaryFullPowerDegree52Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree52Norm,boundaryFullPowerDegree52Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))=c} := by

  have he : ((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))=(boundaryRePowerRow77_21Degree52Norm x).val+(boundaryRePowerRow77_22Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree52Norm x).property (boundaryRePowerRow77_22Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree52Norm,boundaryRePowerRow77_22Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))=(boundaryRePowerRow77_20Degree52Norm x).val+(boundaryFullPowerDegree52Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree52Norm x).property (boundaryFullPowerDegree52Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree52Norm,boundaryFullPowerDegree52Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))))=(boundaryFullPowerDegree52Block16Norm x).val+(boundaryFullPowerDegree52Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block16Norm x).property (boundaryFullPowerDegree52Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block16Norm,boundaryFullPowerDegree52Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))))))=(boundaryFullPowerDegree52Block14Norm x).val+(boundaryFullPowerDegree52Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block14Norm x).property (boundaryFullPowerDegree52Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block14Norm,boundaryFullPowerDegree52Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x)))))))))+(((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x)))))))))+(((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x))))))))))=(boundaryFullPowerDegree52Block9Norm x).val+(boundaryFullPowerDegree52Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block9Norm x).property (boundaryFullPowerDegree52Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block9Norm,boundaryFullPowerDegree52Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x))=c} := by

  have he : ((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x))=(boundaryImPowerRow77_0Degree52Norm x).val+(boundaryImPowerRow77_1Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree52Norm x).property (boundaryImPowerRow77_1Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree52Norm,boundaryImPowerRow77_1Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x))=c} := by

  have he : ((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x))=(boundaryImPowerRow77_3Degree52Norm x).val+(boundaryImPowerRow77_4Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree52Norm x).property (boundaryImPowerRow77_4Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree52Norm,boundaryImPowerRow77_4Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x))))=(boundaryImPowerRow77_2Degree52Norm x).val+(boundaryFullPowerDegree52Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree52Norm x).property (boundaryFullPowerDegree52Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree52Norm,boundaryFullPowerDegree52Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x))))))=(boundaryFullPowerDegree52Block22Norm x).val+(boundaryFullPowerDegree52Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block22Norm x).property (boundaryFullPowerDegree52Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block22Norm,boundaryFullPowerDegree52Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x))=c} := by

  have he : ((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x))=(boundaryImPowerRow77_6Degree52Norm x).val+(boundaryImPowerRow77_7Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree52Norm x).property (boundaryImPowerRow77_7Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree52Norm,boundaryImPowerRow77_7Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x))))=(boundaryImPowerRow77_5Degree52Norm x).val+(boundaryFullPowerDegree52Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree52Norm x).property (boundaryFullPowerDegree52Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree52Norm,boundaryFullPowerDegree52Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))=c} := by

  have he : ((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))=(boundaryImPowerRow77_9Degree52Norm x).val+(boundaryImPowerRow77_10Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree52Norm x).property (boundaryImPowerRow77_10Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree52Norm,boundaryImPowerRow77_10Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))))=(boundaryImPowerRow77_8Degree52Norm x).val+(boundaryFullPowerDegree52Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree52Norm x).property (boundaryFullPowerDegree52Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree52Norm,boundaryFullPowerDegree52Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))))))=(boundaryFullPowerDegree52Block27Norm x).val+(boundaryFullPowerDegree52Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block27Norm x).property (boundaryFullPowerDegree52Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block27Norm,boundaryFullPowerDegree52Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x))))))))=(boundaryFullPowerDegree52Block25Norm x).val+(boundaryFullPowerDegree52Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block25Norm x).property (boundaryFullPowerDegree52Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block25Norm,boundaryFullPowerDegree52Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x))=c} := by

  have he : ((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x))=(boundaryImPowerRow77_12Degree52Norm x).val+(boundaryImPowerRow77_13Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree52Norm x).property (boundaryImPowerRow77_13Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree52Norm,boundaryImPowerRow77_13Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x))))=(boundaryImPowerRow77_11Degree52Norm x).val+(boundaryFullPowerDegree52Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree52Norm x).property (boundaryFullPowerDegree52Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree52Norm,boundaryFullPowerDegree52Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x))=c} := by

  have he : ((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x))=(boundaryImPowerRow77_15Degree52Norm x).val+(boundaryImPowerRow77_16Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree52Norm x).property (boundaryImPowerRow77_16Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree52Norm,boundaryImPowerRow77_16Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x))))=(boundaryImPowerRow77_14Degree52Norm x).val+(boundaryFullPowerDegree52Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree52Norm x).property (boundaryFullPowerDegree52Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree52Norm,boundaryFullPowerDegree52Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x))))))=(boundaryFullPowerDegree52Block33Norm x).val+(boundaryFullPowerDegree52Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block33Norm x).property (boundaryFullPowerDegree52Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block33Norm,boundaryFullPowerDegree52Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x))=c} := by

  have he : ((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x))=(boundaryImPowerRow77_18Degree52Norm x).val+(boundaryImPowerRow77_19Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree52Norm x).property (boundaryImPowerRow77_19Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree52Norm,boundaryImPowerRow77_19Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x))))=(boundaryImPowerRow77_17Degree52Norm x).val+(boundaryFullPowerDegree52Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree52Norm x).property (boundaryFullPowerDegree52Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree52Norm,boundaryFullPowerDegree52Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))=c} := by

  have he : ((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))=(boundaryImPowerRow77_21Degree52Norm x).val+(boundaryLowPowerRow77Degree52Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree52Norm x).property (boundaryLowPowerRow77Degree52Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree52Norm,boundaryLowPowerRow77Degree52Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))=(boundaryImPowerRow77_20Degree52Norm x).val+(boundaryFullPowerDegree52Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree52Norm x).property (boundaryFullPowerDegree52Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree52Norm,boundaryFullPowerDegree52Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))=(boundaryFullPowerDegree52Block38Norm x).val+(boundaryFullPowerDegree52Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block38Norm x).property (boundaryFullPowerDegree52Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block38Norm,boundaryFullPowerDegree52Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))))=(boundaryFullPowerDegree52Block36Norm x).val+(boundaryFullPowerDegree52Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block36Norm x).property (boundaryFullPowerDegree52Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block36Norm,boundaryFullPowerDegree52Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x)))))))))+(((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x)))))))))+(((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))))))=(boundaryFullPowerDegree52Block31Norm x).val+(boundaryFullPowerDegree52Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block31Norm x).property (boundaryFullPowerDegree52Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block31Norm,boundaryFullPowerDegree52Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree52Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x)))))))))+(((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x)))))))))))+(((((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x)))))))))+(((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x)))))))))+(((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x)))))))))))+(((((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x)))))))))+(((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x))))))))))))=(boundaryFullPowerDegree52Block21Norm x).val+(boundaryFullPowerDegree52Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree52Block21Norm x).property (boundaryFullPowerDegree52Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block21Norm,boundaryFullPowerDegree52Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree52Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 52 x=c} := by

  have he0 : boundaryFullPowerRow77 52 x=((((((((((boundaryRePowerRow77_0 52 x)+(boundaryRePowerRow77_1 52 x)))+(((boundaryRePowerRow77_2 52 x)+(((boundaryRePowerRow77_3 52 x)+(boundaryRePowerRow77_4 52 x)))))))+(((((boundaryRePowerRow77_5 52 x)+(((boundaryRePowerRow77_6 52 x)+(boundaryRePowerRow77_7 52 x)))))+(((boundaryRePowerRow77_8 52 x)+(((boundaryRePowerRow77_9 52 x)+(boundaryRePowerRow77_10 52 x)))))))))+(((((((boundaryRePowerRow77_11 52 x)+(((boundaryRePowerRow77_12 52 x)+(boundaryRePowerRow77_13 52 x)))))+(((boundaryRePowerRow77_14 52 x)+(((boundaryRePowerRow77_15 52 x)+(boundaryRePowerRow77_16 52 x)))))))+(((((boundaryRePowerRow77_17 52 x)+(((boundaryRePowerRow77_18 52 x)+(boundaryRePowerRow77_19 52 x)))))+(((boundaryRePowerRow77_20 52 x)+(((boundaryRePowerRow77_21 52 x)+(boundaryRePowerRow77_22 52 x)))))))))))+(((((((((boundaryImPowerRow77_0 52 x)+(boundaryImPowerRow77_1 52 x)))+(((boundaryImPowerRow77_2 52 x)+(((boundaryImPowerRow77_3 52 x)+(boundaryImPowerRow77_4 52 x)))))))+(((((boundaryImPowerRow77_5 52 x)+(((boundaryImPowerRow77_6 52 x)+(boundaryImPowerRow77_7 52 x)))))+(((boundaryImPowerRow77_8 52 x)+(((boundaryImPowerRow77_9 52 x)+(boundaryImPowerRow77_10 52 x)))))))))+(((((((boundaryImPowerRow77_11 52 x)+(((boundaryImPowerRow77_12 52 x)+(boundaryImPowerRow77_13 52 x)))))+(((boundaryImPowerRow77_14 52 x)+(((boundaryImPowerRow77_15 52 x)+(boundaryImPowerRow77_16 52 x)))))))+(((((boundaryImPowerRow77_17 52 x)+(((boundaryImPowerRow77_18 52 x)+(boundaryImPowerRow77_19 52 x)))))+(((boundaryImPowerRow77_20 52 x)+(((boundaryImPowerRow77_21 52 x)+(boundaryLowPowerRow77 52 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree52Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree52Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
