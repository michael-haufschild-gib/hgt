import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree85Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree85Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x))=c} := by

  have he : ((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x))=(boundaryRePowerRow77_0Degree85Norm x).val+(boundaryRePowerRow77_1Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree85Norm x).property (boundaryRePowerRow77_1Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree85Norm,boundaryRePowerRow77_1Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x))=c} := by

  have he : ((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x))=(boundaryRePowerRow77_3Degree85Norm x).val+(boundaryRePowerRow77_4Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree85Norm x).property (boundaryRePowerRow77_4Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree85Norm,boundaryRePowerRow77_4Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x))))=(boundaryRePowerRow77_2Degree85Norm x).val+(boundaryFullPowerDegree85Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree85Norm x).property (boundaryFullPowerDegree85Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree85Norm,boundaryFullPowerDegree85Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x))))))=(boundaryFullPowerDegree85Block0Norm x).val+(boundaryFullPowerDegree85Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block0Norm x).property (boundaryFullPowerDegree85Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block0Norm,boundaryFullPowerDegree85Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x))=c} := by

  have he : ((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x))=(boundaryRePowerRow77_6Degree85Norm x).val+(boundaryRePowerRow77_7Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree85Norm x).property (boundaryRePowerRow77_7Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree85Norm,boundaryRePowerRow77_7Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x))))=(boundaryRePowerRow77_5Degree85Norm x).val+(boundaryFullPowerDegree85Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree85Norm x).property (boundaryFullPowerDegree85Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree85Norm,boundaryFullPowerDegree85Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))=c} := by

  have he : ((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))=(boundaryRePowerRow77_9Degree85Norm x).val+(boundaryRePowerRow77_10Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree85Norm x).property (boundaryRePowerRow77_10Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree85Norm,boundaryRePowerRow77_10Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))))=(boundaryRePowerRow77_8Degree85Norm x).val+(boundaryFullPowerDegree85Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree85Norm x).property (boundaryFullPowerDegree85Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree85Norm,boundaryFullPowerDegree85Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))))))=(boundaryFullPowerDegree85Block5Norm x).val+(boundaryFullPowerDegree85Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block5Norm x).property (boundaryFullPowerDegree85Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block5Norm,boundaryFullPowerDegree85Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x))))))))=(boundaryFullPowerDegree85Block3Norm x).val+(boundaryFullPowerDegree85Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block3Norm x).property (boundaryFullPowerDegree85Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block3Norm,boundaryFullPowerDegree85Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x))=c} := by

  have he : ((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x))=(boundaryRePowerRow77_12Degree85Norm x).val+(boundaryRePowerRow77_13Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree85Norm x).property (boundaryRePowerRow77_13Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree85Norm,boundaryRePowerRow77_13Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x))))=(boundaryRePowerRow77_11Degree85Norm x).val+(boundaryFullPowerDegree85Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree85Norm x).property (boundaryFullPowerDegree85Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree85Norm,boundaryFullPowerDegree85Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x))=c} := by

  have he : ((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x))=(boundaryRePowerRow77_15Degree85Norm x).val+(boundaryRePowerRow77_16Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree85Norm x).property (boundaryRePowerRow77_16Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree85Norm,boundaryRePowerRow77_16Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x))))=(boundaryRePowerRow77_14Degree85Norm x).val+(boundaryFullPowerDegree85Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree85Norm x).property (boundaryFullPowerDegree85Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree85Norm,boundaryFullPowerDegree85Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x))))))=(boundaryFullPowerDegree85Block11Norm x).val+(boundaryFullPowerDegree85Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block11Norm x).property (boundaryFullPowerDegree85Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block11Norm,boundaryFullPowerDegree85Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x))=c} := by

  have he : ((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x))=(boundaryRePowerRow77_18Degree85Norm x).val+(boundaryRePowerRow77_19Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree85Norm x).property (boundaryRePowerRow77_19Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree85Norm,boundaryRePowerRow77_19Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x))))=(boundaryRePowerRow77_17Degree85Norm x).val+(boundaryFullPowerDegree85Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree85Norm x).property (boundaryFullPowerDegree85Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree85Norm,boundaryFullPowerDegree85Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))=c} := by

  have he : ((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))=(boundaryRePowerRow77_21Degree85Norm x).val+(boundaryRePowerRow77_22Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree85Norm x).property (boundaryRePowerRow77_22Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree85Norm,boundaryRePowerRow77_22Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))=(boundaryRePowerRow77_20Degree85Norm x).val+(boundaryFullPowerDegree85Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree85Norm x).property (boundaryFullPowerDegree85Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree85Norm,boundaryFullPowerDegree85Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))))=(boundaryFullPowerDegree85Block16Norm x).val+(boundaryFullPowerDegree85Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block16Norm x).property (boundaryFullPowerDegree85Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block16Norm,boundaryFullPowerDegree85Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))))))=(boundaryFullPowerDegree85Block14Norm x).val+(boundaryFullPowerDegree85Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block14Norm x).property (boundaryFullPowerDegree85Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block14Norm,boundaryFullPowerDegree85Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x)))))))))+(((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x)))))))))+(((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x))))))))))=(boundaryFullPowerDegree85Block9Norm x).val+(boundaryFullPowerDegree85Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block9Norm x).property (boundaryFullPowerDegree85Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block9Norm,boundaryFullPowerDegree85Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x))=c} := by

  have he : ((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x))=(boundaryImPowerRow77_0Degree85Norm x).val+(boundaryImPowerRow77_1Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree85Norm x).property (boundaryImPowerRow77_1Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree85Norm,boundaryImPowerRow77_1Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x))=c} := by

  have he : ((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x))=(boundaryImPowerRow77_3Degree85Norm x).val+(boundaryImPowerRow77_4Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree85Norm x).property (boundaryImPowerRow77_4Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree85Norm,boundaryImPowerRow77_4Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x))))=(boundaryImPowerRow77_2Degree85Norm x).val+(boundaryFullPowerDegree85Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree85Norm x).property (boundaryFullPowerDegree85Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree85Norm,boundaryFullPowerDegree85Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x))))))=(boundaryFullPowerDegree85Block22Norm x).val+(boundaryFullPowerDegree85Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block22Norm x).property (boundaryFullPowerDegree85Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block22Norm,boundaryFullPowerDegree85Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x))=c} := by

  have he : ((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x))=(boundaryImPowerRow77_6Degree85Norm x).val+(boundaryImPowerRow77_7Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree85Norm x).property (boundaryImPowerRow77_7Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree85Norm,boundaryImPowerRow77_7Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x))))=(boundaryImPowerRow77_5Degree85Norm x).val+(boundaryFullPowerDegree85Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree85Norm x).property (boundaryFullPowerDegree85Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree85Norm,boundaryFullPowerDegree85Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))=c} := by

  have he : ((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))=(boundaryImPowerRow77_9Degree85Norm x).val+(boundaryImPowerRow77_10Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree85Norm x).property (boundaryImPowerRow77_10Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree85Norm,boundaryImPowerRow77_10Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))))=(boundaryImPowerRow77_8Degree85Norm x).val+(boundaryFullPowerDegree85Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree85Norm x).property (boundaryFullPowerDegree85Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree85Norm,boundaryFullPowerDegree85Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))))))=(boundaryFullPowerDegree85Block27Norm x).val+(boundaryFullPowerDegree85Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block27Norm x).property (boundaryFullPowerDegree85Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block27Norm,boundaryFullPowerDegree85Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x))))))))=(boundaryFullPowerDegree85Block25Norm x).val+(boundaryFullPowerDegree85Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block25Norm x).property (boundaryFullPowerDegree85Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block25Norm,boundaryFullPowerDegree85Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x))=c} := by

  have he : ((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x))=(boundaryImPowerRow77_12Degree85Norm x).val+(boundaryImPowerRow77_13Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree85Norm x).property (boundaryImPowerRow77_13Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree85Norm,boundaryImPowerRow77_13Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x))))=(boundaryImPowerRow77_11Degree85Norm x).val+(boundaryFullPowerDegree85Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree85Norm x).property (boundaryFullPowerDegree85Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree85Norm,boundaryFullPowerDegree85Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x))=c} := by

  have he : ((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x))=(boundaryImPowerRow77_15Degree85Norm x).val+(boundaryImPowerRow77_16Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree85Norm x).property (boundaryImPowerRow77_16Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree85Norm,boundaryImPowerRow77_16Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x))))=(boundaryImPowerRow77_14Degree85Norm x).val+(boundaryFullPowerDegree85Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree85Norm x).property (boundaryFullPowerDegree85Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree85Norm,boundaryFullPowerDegree85Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x))))))=(boundaryFullPowerDegree85Block33Norm x).val+(boundaryFullPowerDegree85Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block33Norm x).property (boundaryFullPowerDegree85Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block33Norm,boundaryFullPowerDegree85Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x))=c} := by

  have he : ((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x))=(boundaryImPowerRow77_18Degree85Norm x).val+(boundaryImPowerRow77_19Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree85Norm x).property (boundaryImPowerRow77_19Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree85Norm,boundaryImPowerRow77_19Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x))))=(boundaryImPowerRow77_17Degree85Norm x).val+(boundaryFullPowerDegree85Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree85Norm x).property (boundaryFullPowerDegree85Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree85Norm,boundaryFullPowerDegree85Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))=c} := by

  have he : ((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))=(boundaryImPowerRow77_21Degree85Norm x).val+(boundaryLowPowerRow77Degree85Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree85Norm x).property (boundaryLowPowerRow77Degree85Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree85Norm,boundaryLowPowerRow77Degree85Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))=(boundaryImPowerRow77_20Degree85Norm x).val+(boundaryFullPowerDegree85Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree85Norm x).property (boundaryFullPowerDegree85Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree85Norm,boundaryFullPowerDegree85Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))=(boundaryFullPowerDegree85Block38Norm x).val+(boundaryFullPowerDegree85Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block38Norm x).property (boundaryFullPowerDegree85Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block38Norm,boundaryFullPowerDegree85Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))))=(boundaryFullPowerDegree85Block36Norm x).val+(boundaryFullPowerDegree85Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block36Norm x).property (boundaryFullPowerDegree85Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block36Norm,boundaryFullPowerDegree85Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x)))))))))+(((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x)))))))))+(((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))))))=(boundaryFullPowerDegree85Block31Norm x).val+(boundaryFullPowerDegree85Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block31Norm x).property (boundaryFullPowerDegree85Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block31Norm,boundaryFullPowerDegree85Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree85Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x)))))))))+(((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x)))))))))))+(((((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x)))))))))+(((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x)))))))))+(((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x)))))))))))+(((((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x)))))))))+(((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x))))))))))))=(boundaryFullPowerDegree85Block21Norm x).val+(boundaryFullPowerDegree85Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree85Block21Norm x).property (boundaryFullPowerDegree85Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block21Norm,boundaryFullPowerDegree85Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree85Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 85 x=c} := by

  have he0 : boundaryFullPowerRow77 85 x=((((((((((boundaryRePowerRow77_0 85 x)+(boundaryRePowerRow77_1 85 x)))+(((boundaryRePowerRow77_2 85 x)+(((boundaryRePowerRow77_3 85 x)+(boundaryRePowerRow77_4 85 x)))))))+(((((boundaryRePowerRow77_5 85 x)+(((boundaryRePowerRow77_6 85 x)+(boundaryRePowerRow77_7 85 x)))))+(((boundaryRePowerRow77_8 85 x)+(((boundaryRePowerRow77_9 85 x)+(boundaryRePowerRow77_10 85 x)))))))))+(((((((boundaryRePowerRow77_11 85 x)+(((boundaryRePowerRow77_12 85 x)+(boundaryRePowerRow77_13 85 x)))))+(((boundaryRePowerRow77_14 85 x)+(((boundaryRePowerRow77_15 85 x)+(boundaryRePowerRow77_16 85 x)))))))+(((((boundaryRePowerRow77_17 85 x)+(((boundaryRePowerRow77_18 85 x)+(boundaryRePowerRow77_19 85 x)))))+(((boundaryRePowerRow77_20 85 x)+(((boundaryRePowerRow77_21 85 x)+(boundaryRePowerRow77_22 85 x)))))))))))+(((((((((boundaryImPowerRow77_0 85 x)+(boundaryImPowerRow77_1 85 x)))+(((boundaryImPowerRow77_2 85 x)+(((boundaryImPowerRow77_3 85 x)+(boundaryImPowerRow77_4 85 x)))))))+(((((boundaryImPowerRow77_5 85 x)+(((boundaryImPowerRow77_6 85 x)+(boundaryImPowerRow77_7 85 x)))))+(((boundaryImPowerRow77_8 85 x)+(((boundaryImPowerRow77_9 85 x)+(boundaryImPowerRow77_10 85 x)))))))))+(((((((boundaryImPowerRow77_11 85 x)+(((boundaryImPowerRow77_12 85 x)+(boundaryImPowerRow77_13 85 x)))))+(((boundaryImPowerRow77_14 85 x)+(((boundaryImPowerRow77_15 85 x)+(boundaryImPowerRow77_16 85 x)))))))+(((((boundaryImPowerRow77_17 85 x)+(((boundaryImPowerRow77_18 85 x)+(boundaryImPowerRow77_19 85 x)))))+(((boundaryImPowerRow77_20 85 x)+(((boundaryImPowerRow77_21 85 x)+(boundaryLowPowerRow77 85 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree85Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree85Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
