import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree49Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree49Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x))=c} := by

  have he : ((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x))=(boundaryRePowerRow77_0Degree49Norm x).val+(boundaryRePowerRow77_1Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree49Norm x).property (boundaryRePowerRow77_1Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree49Norm,boundaryRePowerRow77_1Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x))=c} := by

  have he : ((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x))=(boundaryRePowerRow77_3Degree49Norm x).val+(boundaryRePowerRow77_4Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree49Norm x).property (boundaryRePowerRow77_4Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree49Norm,boundaryRePowerRow77_4Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x))))=(boundaryRePowerRow77_2Degree49Norm x).val+(boundaryFullPowerDegree49Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree49Norm x).property (boundaryFullPowerDegree49Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree49Norm,boundaryFullPowerDegree49Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x))))))=(boundaryFullPowerDegree49Block0Norm x).val+(boundaryFullPowerDegree49Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block0Norm x).property (boundaryFullPowerDegree49Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block0Norm,boundaryFullPowerDegree49Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x))=c} := by

  have he : ((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x))=(boundaryRePowerRow77_6Degree49Norm x).val+(boundaryRePowerRow77_7Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree49Norm x).property (boundaryRePowerRow77_7Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree49Norm,boundaryRePowerRow77_7Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x))))=(boundaryRePowerRow77_5Degree49Norm x).val+(boundaryFullPowerDegree49Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree49Norm x).property (boundaryFullPowerDegree49Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree49Norm,boundaryFullPowerDegree49Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))=c} := by

  have he : ((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))=(boundaryRePowerRow77_9Degree49Norm x).val+(boundaryRePowerRow77_10Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree49Norm x).property (boundaryRePowerRow77_10Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree49Norm,boundaryRePowerRow77_10Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))))=(boundaryRePowerRow77_8Degree49Norm x).val+(boundaryFullPowerDegree49Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree49Norm x).property (boundaryFullPowerDegree49Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree49Norm,boundaryFullPowerDegree49Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))))))=(boundaryFullPowerDegree49Block5Norm x).val+(boundaryFullPowerDegree49Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block5Norm x).property (boundaryFullPowerDegree49Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block5Norm,boundaryFullPowerDegree49Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x))))))))=(boundaryFullPowerDegree49Block3Norm x).val+(boundaryFullPowerDegree49Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block3Norm x).property (boundaryFullPowerDegree49Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block3Norm,boundaryFullPowerDegree49Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x))=c} := by

  have he : ((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x))=(boundaryRePowerRow77_12Degree49Norm x).val+(boundaryRePowerRow77_13Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree49Norm x).property (boundaryRePowerRow77_13Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree49Norm,boundaryRePowerRow77_13Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x))))=(boundaryRePowerRow77_11Degree49Norm x).val+(boundaryFullPowerDegree49Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree49Norm x).property (boundaryFullPowerDegree49Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree49Norm,boundaryFullPowerDegree49Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x))=c} := by

  have he : ((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x))=(boundaryRePowerRow77_15Degree49Norm x).val+(boundaryRePowerRow77_16Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree49Norm x).property (boundaryRePowerRow77_16Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree49Norm,boundaryRePowerRow77_16Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x))))=(boundaryRePowerRow77_14Degree49Norm x).val+(boundaryFullPowerDegree49Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree49Norm x).property (boundaryFullPowerDegree49Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree49Norm,boundaryFullPowerDegree49Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x))))))=(boundaryFullPowerDegree49Block11Norm x).val+(boundaryFullPowerDegree49Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block11Norm x).property (boundaryFullPowerDegree49Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block11Norm,boundaryFullPowerDegree49Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x))=c} := by

  have he : ((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x))=(boundaryRePowerRow77_18Degree49Norm x).val+(boundaryRePowerRow77_19Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree49Norm x).property (boundaryRePowerRow77_19Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree49Norm,boundaryRePowerRow77_19Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x))))=(boundaryRePowerRow77_17Degree49Norm x).val+(boundaryFullPowerDegree49Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree49Norm x).property (boundaryFullPowerDegree49Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree49Norm,boundaryFullPowerDegree49Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))=c} := by

  have he : ((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))=(boundaryRePowerRow77_21Degree49Norm x).val+(boundaryRePowerRow77_22Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree49Norm x).property (boundaryRePowerRow77_22Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree49Norm,boundaryRePowerRow77_22Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))=(boundaryRePowerRow77_20Degree49Norm x).val+(boundaryFullPowerDegree49Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree49Norm x).property (boundaryFullPowerDegree49Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree49Norm,boundaryFullPowerDegree49Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))))=(boundaryFullPowerDegree49Block16Norm x).val+(boundaryFullPowerDegree49Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block16Norm x).property (boundaryFullPowerDegree49Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block16Norm,boundaryFullPowerDegree49Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))))))=(boundaryFullPowerDegree49Block14Norm x).val+(boundaryFullPowerDegree49Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block14Norm x).property (boundaryFullPowerDegree49Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block14Norm,boundaryFullPowerDegree49Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x)))))))))+(((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x)))))))))+(((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x))))))))))=(boundaryFullPowerDegree49Block9Norm x).val+(boundaryFullPowerDegree49Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block9Norm x).property (boundaryFullPowerDegree49Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block9Norm,boundaryFullPowerDegree49Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x))=c} := by

  have he : ((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x))=(boundaryImPowerRow77_0Degree49Norm x).val+(boundaryImPowerRow77_1Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree49Norm x).property (boundaryImPowerRow77_1Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree49Norm,boundaryImPowerRow77_1Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x))=c} := by

  have he : ((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x))=(boundaryImPowerRow77_3Degree49Norm x).val+(boundaryImPowerRow77_4Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree49Norm x).property (boundaryImPowerRow77_4Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree49Norm,boundaryImPowerRow77_4Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x))))=(boundaryImPowerRow77_2Degree49Norm x).val+(boundaryFullPowerDegree49Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree49Norm x).property (boundaryFullPowerDegree49Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree49Norm,boundaryFullPowerDegree49Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x))))))=(boundaryFullPowerDegree49Block22Norm x).val+(boundaryFullPowerDegree49Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block22Norm x).property (boundaryFullPowerDegree49Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block22Norm,boundaryFullPowerDegree49Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x))=c} := by

  have he : ((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x))=(boundaryImPowerRow77_6Degree49Norm x).val+(boundaryImPowerRow77_7Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree49Norm x).property (boundaryImPowerRow77_7Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree49Norm,boundaryImPowerRow77_7Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x))))=(boundaryImPowerRow77_5Degree49Norm x).val+(boundaryFullPowerDegree49Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree49Norm x).property (boundaryFullPowerDegree49Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree49Norm,boundaryFullPowerDegree49Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))=c} := by

  have he : ((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))=(boundaryImPowerRow77_9Degree49Norm x).val+(boundaryImPowerRow77_10Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree49Norm x).property (boundaryImPowerRow77_10Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree49Norm,boundaryImPowerRow77_10Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))))=(boundaryImPowerRow77_8Degree49Norm x).val+(boundaryFullPowerDegree49Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree49Norm x).property (boundaryFullPowerDegree49Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree49Norm,boundaryFullPowerDegree49Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))))))=(boundaryFullPowerDegree49Block27Norm x).val+(boundaryFullPowerDegree49Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block27Norm x).property (boundaryFullPowerDegree49Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block27Norm,boundaryFullPowerDegree49Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x))))))))=(boundaryFullPowerDegree49Block25Norm x).val+(boundaryFullPowerDegree49Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block25Norm x).property (boundaryFullPowerDegree49Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block25Norm,boundaryFullPowerDegree49Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x))=c} := by

  have he : ((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x))=(boundaryImPowerRow77_12Degree49Norm x).val+(boundaryImPowerRow77_13Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree49Norm x).property (boundaryImPowerRow77_13Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree49Norm,boundaryImPowerRow77_13Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x))))=(boundaryImPowerRow77_11Degree49Norm x).val+(boundaryFullPowerDegree49Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree49Norm x).property (boundaryFullPowerDegree49Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree49Norm,boundaryFullPowerDegree49Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x))=c} := by

  have he : ((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x))=(boundaryImPowerRow77_15Degree49Norm x).val+(boundaryImPowerRow77_16Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree49Norm x).property (boundaryImPowerRow77_16Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree49Norm,boundaryImPowerRow77_16Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x))))=(boundaryImPowerRow77_14Degree49Norm x).val+(boundaryFullPowerDegree49Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree49Norm x).property (boundaryFullPowerDegree49Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree49Norm,boundaryFullPowerDegree49Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x))))))=(boundaryFullPowerDegree49Block33Norm x).val+(boundaryFullPowerDegree49Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block33Norm x).property (boundaryFullPowerDegree49Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block33Norm,boundaryFullPowerDegree49Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x))=c} := by

  have he : ((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x))=(boundaryImPowerRow77_18Degree49Norm x).val+(boundaryImPowerRow77_19Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree49Norm x).property (boundaryImPowerRow77_19Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree49Norm,boundaryImPowerRow77_19Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x))))=(boundaryImPowerRow77_17Degree49Norm x).val+(boundaryFullPowerDegree49Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree49Norm x).property (boundaryFullPowerDegree49Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree49Norm,boundaryFullPowerDegree49Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))=c} := by

  have he : ((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))=(boundaryImPowerRow77_21Degree49Norm x).val+(boundaryLowPowerRow77Degree49Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree49Norm x).property (boundaryLowPowerRow77Degree49Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree49Norm,boundaryLowPowerRow77Degree49Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))=(boundaryImPowerRow77_20Degree49Norm x).val+(boundaryFullPowerDegree49Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree49Norm x).property (boundaryFullPowerDegree49Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree49Norm,boundaryFullPowerDegree49Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))=(boundaryFullPowerDegree49Block38Norm x).val+(boundaryFullPowerDegree49Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block38Norm x).property (boundaryFullPowerDegree49Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block38Norm,boundaryFullPowerDegree49Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))))=(boundaryFullPowerDegree49Block36Norm x).val+(boundaryFullPowerDegree49Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block36Norm x).property (boundaryFullPowerDegree49Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block36Norm,boundaryFullPowerDegree49Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x)))))))))+(((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x)))))))))+(((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))))))=(boundaryFullPowerDegree49Block31Norm x).val+(boundaryFullPowerDegree49Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block31Norm x).property (boundaryFullPowerDegree49Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block31Norm,boundaryFullPowerDegree49Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree49Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x)))))))))+(((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x)))))))))))+(((((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x)))))))))+(((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x)))))))))+(((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x)))))))))))+(((((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x)))))))))+(((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x))))))))))))=(boundaryFullPowerDegree49Block21Norm x).val+(boundaryFullPowerDegree49Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree49Block21Norm x).property (boundaryFullPowerDegree49Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block21Norm,boundaryFullPowerDegree49Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree49Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 49 x=c} := by

  have he0 : boundaryFullPowerRow77 49 x=((((((((((boundaryRePowerRow77_0 49 x)+(boundaryRePowerRow77_1 49 x)))+(((boundaryRePowerRow77_2 49 x)+(((boundaryRePowerRow77_3 49 x)+(boundaryRePowerRow77_4 49 x)))))))+(((((boundaryRePowerRow77_5 49 x)+(((boundaryRePowerRow77_6 49 x)+(boundaryRePowerRow77_7 49 x)))))+(((boundaryRePowerRow77_8 49 x)+(((boundaryRePowerRow77_9 49 x)+(boundaryRePowerRow77_10 49 x)))))))))+(((((((boundaryRePowerRow77_11 49 x)+(((boundaryRePowerRow77_12 49 x)+(boundaryRePowerRow77_13 49 x)))))+(((boundaryRePowerRow77_14 49 x)+(((boundaryRePowerRow77_15 49 x)+(boundaryRePowerRow77_16 49 x)))))))+(((((boundaryRePowerRow77_17 49 x)+(((boundaryRePowerRow77_18 49 x)+(boundaryRePowerRow77_19 49 x)))))+(((boundaryRePowerRow77_20 49 x)+(((boundaryRePowerRow77_21 49 x)+(boundaryRePowerRow77_22 49 x)))))))))))+(((((((((boundaryImPowerRow77_0 49 x)+(boundaryImPowerRow77_1 49 x)))+(((boundaryImPowerRow77_2 49 x)+(((boundaryImPowerRow77_3 49 x)+(boundaryImPowerRow77_4 49 x)))))))+(((((boundaryImPowerRow77_5 49 x)+(((boundaryImPowerRow77_6 49 x)+(boundaryImPowerRow77_7 49 x)))))+(((boundaryImPowerRow77_8 49 x)+(((boundaryImPowerRow77_9 49 x)+(boundaryImPowerRow77_10 49 x)))))))))+(((((((boundaryImPowerRow77_11 49 x)+(((boundaryImPowerRow77_12 49 x)+(boundaryImPowerRow77_13 49 x)))))+(((boundaryImPowerRow77_14 49 x)+(((boundaryImPowerRow77_15 49 x)+(boundaryImPowerRow77_16 49 x)))))))+(((((boundaryImPowerRow77_17 49 x)+(((boundaryImPowerRow77_18 49 x)+(boundaryImPowerRow77_19 49 x)))))+(((boundaryImPowerRow77_20 49 x)+(((boundaryImPowerRow77_21 49 x)+(boundaryLowPowerRow77 49 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree49Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree49Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
