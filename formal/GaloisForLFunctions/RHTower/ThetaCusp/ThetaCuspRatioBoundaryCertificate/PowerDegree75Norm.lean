import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree75Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree75Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x))=c} := by

  have he : ((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x))=(boundaryRePowerRow77_0Degree75Norm x).val+(boundaryRePowerRow77_1Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree75Norm x).property (boundaryRePowerRow77_1Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree75Norm,boundaryRePowerRow77_1Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x))=c} := by

  have he : ((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x))=(boundaryRePowerRow77_3Degree75Norm x).val+(boundaryRePowerRow77_4Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree75Norm x).property (boundaryRePowerRow77_4Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree75Norm,boundaryRePowerRow77_4Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x))))=(boundaryRePowerRow77_2Degree75Norm x).val+(boundaryFullPowerDegree75Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree75Norm x).property (boundaryFullPowerDegree75Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree75Norm,boundaryFullPowerDegree75Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x))))))=(boundaryFullPowerDegree75Block0Norm x).val+(boundaryFullPowerDegree75Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block0Norm x).property (boundaryFullPowerDegree75Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block0Norm,boundaryFullPowerDegree75Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x))=c} := by

  have he : ((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x))=(boundaryRePowerRow77_6Degree75Norm x).val+(boundaryRePowerRow77_7Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree75Norm x).property (boundaryRePowerRow77_7Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree75Norm,boundaryRePowerRow77_7Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x))))=(boundaryRePowerRow77_5Degree75Norm x).val+(boundaryFullPowerDegree75Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree75Norm x).property (boundaryFullPowerDegree75Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree75Norm,boundaryFullPowerDegree75Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))=c} := by

  have he : ((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))=(boundaryRePowerRow77_9Degree75Norm x).val+(boundaryRePowerRow77_10Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree75Norm x).property (boundaryRePowerRow77_10Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree75Norm,boundaryRePowerRow77_10Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))))=(boundaryRePowerRow77_8Degree75Norm x).val+(boundaryFullPowerDegree75Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree75Norm x).property (boundaryFullPowerDegree75Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree75Norm,boundaryFullPowerDegree75Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))))))=(boundaryFullPowerDegree75Block5Norm x).val+(boundaryFullPowerDegree75Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block5Norm x).property (boundaryFullPowerDegree75Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block5Norm,boundaryFullPowerDegree75Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x))))))))=(boundaryFullPowerDegree75Block3Norm x).val+(boundaryFullPowerDegree75Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block3Norm x).property (boundaryFullPowerDegree75Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block3Norm,boundaryFullPowerDegree75Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x))=c} := by

  have he : ((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x))=(boundaryRePowerRow77_12Degree75Norm x).val+(boundaryRePowerRow77_13Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree75Norm x).property (boundaryRePowerRow77_13Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree75Norm,boundaryRePowerRow77_13Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x))))=(boundaryRePowerRow77_11Degree75Norm x).val+(boundaryFullPowerDegree75Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree75Norm x).property (boundaryFullPowerDegree75Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree75Norm,boundaryFullPowerDegree75Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x))=c} := by

  have he : ((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x))=(boundaryRePowerRow77_15Degree75Norm x).val+(boundaryRePowerRow77_16Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree75Norm x).property (boundaryRePowerRow77_16Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree75Norm,boundaryRePowerRow77_16Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x))))=(boundaryRePowerRow77_14Degree75Norm x).val+(boundaryFullPowerDegree75Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree75Norm x).property (boundaryFullPowerDegree75Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree75Norm,boundaryFullPowerDegree75Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x))))))=(boundaryFullPowerDegree75Block11Norm x).val+(boundaryFullPowerDegree75Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block11Norm x).property (boundaryFullPowerDegree75Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block11Norm,boundaryFullPowerDegree75Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x))=c} := by

  have he : ((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x))=(boundaryRePowerRow77_18Degree75Norm x).val+(boundaryRePowerRow77_19Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree75Norm x).property (boundaryRePowerRow77_19Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree75Norm,boundaryRePowerRow77_19Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x))))=(boundaryRePowerRow77_17Degree75Norm x).val+(boundaryFullPowerDegree75Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree75Norm x).property (boundaryFullPowerDegree75Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree75Norm,boundaryFullPowerDegree75Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))=c} := by

  have he : ((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))=(boundaryRePowerRow77_21Degree75Norm x).val+(boundaryRePowerRow77_22Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree75Norm x).property (boundaryRePowerRow77_22Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree75Norm,boundaryRePowerRow77_22Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))=(boundaryRePowerRow77_20Degree75Norm x).val+(boundaryFullPowerDegree75Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree75Norm x).property (boundaryFullPowerDegree75Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree75Norm,boundaryFullPowerDegree75Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))))=(boundaryFullPowerDegree75Block16Norm x).val+(boundaryFullPowerDegree75Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block16Norm x).property (boundaryFullPowerDegree75Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block16Norm,boundaryFullPowerDegree75Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))))))=(boundaryFullPowerDegree75Block14Norm x).val+(boundaryFullPowerDegree75Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block14Norm x).property (boundaryFullPowerDegree75Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block14Norm,boundaryFullPowerDegree75Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x)))))))))+(((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x)))))))))+(((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x))))))))))=(boundaryFullPowerDegree75Block9Norm x).val+(boundaryFullPowerDegree75Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block9Norm x).property (boundaryFullPowerDegree75Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block9Norm,boundaryFullPowerDegree75Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x))=c} := by

  have he : ((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x))=(boundaryImPowerRow77_0Degree75Norm x).val+(boundaryImPowerRow77_1Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree75Norm x).property (boundaryImPowerRow77_1Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree75Norm,boundaryImPowerRow77_1Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x))=c} := by

  have he : ((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x))=(boundaryImPowerRow77_3Degree75Norm x).val+(boundaryImPowerRow77_4Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree75Norm x).property (boundaryImPowerRow77_4Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree75Norm,boundaryImPowerRow77_4Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x))))=(boundaryImPowerRow77_2Degree75Norm x).val+(boundaryFullPowerDegree75Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree75Norm x).property (boundaryFullPowerDegree75Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree75Norm,boundaryFullPowerDegree75Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x))))))=(boundaryFullPowerDegree75Block22Norm x).val+(boundaryFullPowerDegree75Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block22Norm x).property (boundaryFullPowerDegree75Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block22Norm,boundaryFullPowerDegree75Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x))=c} := by

  have he : ((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x))=(boundaryImPowerRow77_6Degree75Norm x).val+(boundaryImPowerRow77_7Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree75Norm x).property (boundaryImPowerRow77_7Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree75Norm,boundaryImPowerRow77_7Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x))))=(boundaryImPowerRow77_5Degree75Norm x).val+(boundaryFullPowerDegree75Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree75Norm x).property (boundaryFullPowerDegree75Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree75Norm,boundaryFullPowerDegree75Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))=c} := by

  have he : ((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))=(boundaryImPowerRow77_9Degree75Norm x).val+(boundaryImPowerRow77_10Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree75Norm x).property (boundaryImPowerRow77_10Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree75Norm,boundaryImPowerRow77_10Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))))=(boundaryImPowerRow77_8Degree75Norm x).val+(boundaryFullPowerDegree75Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree75Norm x).property (boundaryFullPowerDegree75Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree75Norm,boundaryFullPowerDegree75Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))))))=(boundaryFullPowerDegree75Block27Norm x).val+(boundaryFullPowerDegree75Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block27Norm x).property (boundaryFullPowerDegree75Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block27Norm,boundaryFullPowerDegree75Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x))))))))=(boundaryFullPowerDegree75Block25Norm x).val+(boundaryFullPowerDegree75Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block25Norm x).property (boundaryFullPowerDegree75Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block25Norm,boundaryFullPowerDegree75Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x))=c} := by

  have he : ((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x))=(boundaryImPowerRow77_12Degree75Norm x).val+(boundaryImPowerRow77_13Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree75Norm x).property (boundaryImPowerRow77_13Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree75Norm,boundaryImPowerRow77_13Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x))))=(boundaryImPowerRow77_11Degree75Norm x).val+(boundaryFullPowerDegree75Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree75Norm x).property (boundaryFullPowerDegree75Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree75Norm,boundaryFullPowerDegree75Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x))=c} := by

  have he : ((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x))=(boundaryImPowerRow77_15Degree75Norm x).val+(boundaryImPowerRow77_16Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree75Norm x).property (boundaryImPowerRow77_16Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree75Norm,boundaryImPowerRow77_16Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x))))=(boundaryImPowerRow77_14Degree75Norm x).val+(boundaryFullPowerDegree75Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree75Norm x).property (boundaryFullPowerDegree75Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree75Norm,boundaryFullPowerDegree75Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x))))))=(boundaryFullPowerDegree75Block33Norm x).val+(boundaryFullPowerDegree75Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block33Norm x).property (boundaryFullPowerDegree75Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block33Norm,boundaryFullPowerDegree75Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x))=c} := by

  have he : ((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x))=(boundaryImPowerRow77_18Degree75Norm x).val+(boundaryImPowerRow77_19Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree75Norm x).property (boundaryImPowerRow77_19Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree75Norm,boundaryImPowerRow77_19Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x))))=(boundaryImPowerRow77_17Degree75Norm x).val+(boundaryFullPowerDegree75Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree75Norm x).property (boundaryFullPowerDegree75Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree75Norm,boundaryFullPowerDegree75Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))=c} := by

  have he : ((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))=(boundaryImPowerRow77_21Degree75Norm x).val+(boundaryLowPowerRow77Degree75Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree75Norm x).property (boundaryLowPowerRow77Degree75Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree75Norm,boundaryLowPowerRow77Degree75Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))=(boundaryImPowerRow77_20Degree75Norm x).val+(boundaryFullPowerDegree75Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree75Norm x).property (boundaryFullPowerDegree75Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree75Norm,boundaryFullPowerDegree75Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))=(boundaryFullPowerDegree75Block38Norm x).val+(boundaryFullPowerDegree75Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block38Norm x).property (boundaryFullPowerDegree75Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block38Norm,boundaryFullPowerDegree75Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))))=(boundaryFullPowerDegree75Block36Norm x).val+(boundaryFullPowerDegree75Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block36Norm x).property (boundaryFullPowerDegree75Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block36Norm,boundaryFullPowerDegree75Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x)))))))))+(((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x)))))))))+(((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))))))=(boundaryFullPowerDegree75Block31Norm x).val+(boundaryFullPowerDegree75Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block31Norm x).property (boundaryFullPowerDegree75Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block31Norm,boundaryFullPowerDegree75Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree75Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x)))))))))+(((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x)))))))))))+(((((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x)))))))))+(((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x)))))))))+(((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x)))))))))))+(((((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x)))))))))+(((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x))))))))))))=(boundaryFullPowerDegree75Block21Norm x).val+(boundaryFullPowerDegree75Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree75Block21Norm x).property (boundaryFullPowerDegree75Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block21Norm,boundaryFullPowerDegree75Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree75Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 75 x=c} := by

  have he0 : boundaryFullPowerRow77 75 x=((((((((((boundaryRePowerRow77_0 75 x)+(boundaryRePowerRow77_1 75 x)))+(((boundaryRePowerRow77_2 75 x)+(((boundaryRePowerRow77_3 75 x)+(boundaryRePowerRow77_4 75 x)))))))+(((((boundaryRePowerRow77_5 75 x)+(((boundaryRePowerRow77_6 75 x)+(boundaryRePowerRow77_7 75 x)))))+(((boundaryRePowerRow77_8 75 x)+(((boundaryRePowerRow77_9 75 x)+(boundaryRePowerRow77_10 75 x)))))))))+(((((((boundaryRePowerRow77_11 75 x)+(((boundaryRePowerRow77_12 75 x)+(boundaryRePowerRow77_13 75 x)))))+(((boundaryRePowerRow77_14 75 x)+(((boundaryRePowerRow77_15 75 x)+(boundaryRePowerRow77_16 75 x)))))))+(((((boundaryRePowerRow77_17 75 x)+(((boundaryRePowerRow77_18 75 x)+(boundaryRePowerRow77_19 75 x)))))+(((boundaryRePowerRow77_20 75 x)+(((boundaryRePowerRow77_21 75 x)+(boundaryRePowerRow77_22 75 x)))))))))))+(((((((((boundaryImPowerRow77_0 75 x)+(boundaryImPowerRow77_1 75 x)))+(((boundaryImPowerRow77_2 75 x)+(((boundaryImPowerRow77_3 75 x)+(boundaryImPowerRow77_4 75 x)))))))+(((((boundaryImPowerRow77_5 75 x)+(((boundaryImPowerRow77_6 75 x)+(boundaryImPowerRow77_7 75 x)))))+(((boundaryImPowerRow77_8 75 x)+(((boundaryImPowerRow77_9 75 x)+(boundaryImPowerRow77_10 75 x)))))))))+(((((((boundaryImPowerRow77_11 75 x)+(((boundaryImPowerRow77_12 75 x)+(boundaryImPowerRow77_13 75 x)))))+(((boundaryImPowerRow77_14 75 x)+(((boundaryImPowerRow77_15 75 x)+(boundaryImPowerRow77_16 75 x)))))))+(((((boundaryImPowerRow77_17 75 x)+(((boundaryImPowerRow77_18 75 x)+(boundaryImPowerRow77_19 75 x)))))+(((boundaryImPowerRow77_20 75 x)+(((boundaryImPowerRow77_21 75 x)+(boundaryLowPowerRow77 75 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree75Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree75Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
