import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree10Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree10Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x))=c} := by

  have he : ((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x))=(boundaryRePowerRow77_0Degree10Norm x).val+(boundaryRePowerRow77_1Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree10Norm x).property (boundaryRePowerRow77_1Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree10Norm,boundaryRePowerRow77_1Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x))=c} := by

  have he : ((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x))=(boundaryRePowerRow77_3Degree10Norm x).val+(boundaryRePowerRow77_4Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree10Norm x).property (boundaryRePowerRow77_4Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree10Norm,boundaryRePowerRow77_4Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x))))=(boundaryRePowerRow77_2Degree10Norm x).val+(boundaryFullPowerDegree10Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree10Norm x).property (boundaryFullPowerDegree10Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree10Norm,boundaryFullPowerDegree10Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x))))))=(boundaryFullPowerDegree10Block0Norm x).val+(boundaryFullPowerDegree10Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block0Norm x).property (boundaryFullPowerDegree10Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block0Norm,boundaryFullPowerDegree10Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x))=c} := by

  have he : ((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x))=(boundaryRePowerRow77_6Degree10Norm x).val+(boundaryRePowerRow77_7Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree10Norm x).property (boundaryRePowerRow77_7Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree10Norm,boundaryRePowerRow77_7Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x))))=(boundaryRePowerRow77_5Degree10Norm x).val+(boundaryFullPowerDegree10Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree10Norm x).property (boundaryFullPowerDegree10Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree10Norm,boundaryFullPowerDegree10Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))=c} := by

  have he : ((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))=(boundaryRePowerRow77_9Degree10Norm x).val+(boundaryRePowerRow77_10Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree10Norm x).property (boundaryRePowerRow77_10Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree10Norm,boundaryRePowerRow77_10Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))))=(boundaryRePowerRow77_8Degree10Norm x).val+(boundaryFullPowerDegree10Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree10Norm x).property (boundaryFullPowerDegree10Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree10Norm,boundaryFullPowerDegree10Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))))))=(boundaryFullPowerDegree10Block5Norm x).val+(boundaryFullPowerDegree10Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block5Norm x).property (boundaryFullPowerDegree10Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block5Norm,boundaryFullPowerDegree10Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x))))))))=(boundaryFullPowerDegree10Block3Norm x).val+(boundaryFullPowerDegree10Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block3Norm x).property (boundaryFullPowerDegree10Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block3Norm,boundaryFullPowerDegree10Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x))=c} := by

  have he : ((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x))=(boundaryRePowerRow77_12Degree10Norm x).val+(boundaryRePowerRow77_13Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree10Norm x).property (boundaryRePowerRow77_13Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree10Norm,boundaryRePowerRow77_13Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x))))=(boundaryRePowerRow77_11Degree10Norm x).val+(boundaryFullPowerDegree10Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree10Norm x).property (boundaryFullPowerDegree10Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree10Norm,boundaryFullPowerDegree10Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x))=c} := by

  have he : ((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x))=(boundaryRePowerRow77_15Degree10Norm x).val+(boundaryRePowerRow77_16Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree10Norm x).property (boundaryRePowerRow77_16Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree10Norm,boundaryRePowerRow77_16Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x))))=(boundaryRePowerRow77_14Degree10Norm x).val+(boundaryFullPowerDegree10Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree10Norm x).property (boundaryFullPowerDegree10Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree10Norm,boundaryFullPowerDegree10Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x))))))=(boundaryFullPowerDegree10Block11Norm x).val+(boundaryFullPowerDegree10Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block11Norm x).property (boundaryFullPowerDegree10Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block11Norm,boundaryFullPowerDegree10Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x))=c} := by

  have he : ((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x))=(boundaryRePowerRow77_18Degree10Norm x).val+(boundaryRePowerRow77_19Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree10Norm x).property (boundaryRePowerRow77_19Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree10Norm,boundaryRePowerRow77_19Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x))))=(boundaryRePowerRow77_17Degree10Norm x).val+(boundaryFullPowerDegree10Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree10Norm x).property (boundaryFullPowerDegree10Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree10Norm,boundaryFullPowerDegree10Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))=c} := by

  have he : ((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))=(boundaryRePowerRow77_21Degree10Norm x).val+(boundaryRePowerRow77_22Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree10Norm x).property (boundaryRePowerRow77_22Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree10Norm,boundaryRePowerRow77_22Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))=(boundaryRePowerRow77_20Degree10Norm x).val+(boundaryFullPowerDegree10Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree10Norm x).property (boundaryFullPowerDegree10Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree10Norm,boundaryFullPowerDegree10Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))))=(boundaryFullPowerDegree10Block16Norm x).val+(boundaryFullPowerDegree10Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block16Norm x).property (boundaryFullPowerDegree10Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block16Norm,boundaryFullPowerDegree10Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))))))=(boundaryFullPowerDegree10Block14Norm x).val+(boundaryFullPowerDegree10Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block14Norm x).property (boundaryFullPowerDegree10Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block14Norm,boundaryFullPowerDegree10Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x)))))))))+(((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x)))))))))+(((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x))))))))))=(boundaryFullPowerDegree10Block9Norm x).val+(boundaryFullPowerDegree10Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block9Norm x).property (boundaryFullPowerDegree10Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block9Norm,boundaryFullPowerDegree10Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x))=c} := by

  have he : ((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x))=(boundaryImPowerRow77_0Degree10Norm x).val+(boundaryImPowerRow77_1Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree10Norm x).property (boundaryImPowerRow77_1Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree10Norm,boundaryImPowerRow77_1Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x))=c} := by

  have he : ((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x))=(boundaryImPowerRow77_3Degree10Norm x).val+(boundaryImPowerRow77_4Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree10Norm x).property (boundaryImPowerRow77_4Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree10Norm,boundaryImPowerRow77_4Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x))))=(boundaryImPowerRow77_2Degree10Norm x).val+(boundaryFullPowerDegree10Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree10Norm x).property (boundaryFullPowerDegree10Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree10Norm,boundaryFullPowerDegree10Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x))))))=(boundaryFullPowerDegree10Block22Norm x).val+(boundaryFullPowerDegree10Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block22Norm x).property (boundaryFullPowerDegree10Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block22Norm,boundaryFullPowerDegree10Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x))=c} := by

  have he : ((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x))=(boundaryImPowerRow77_6Degree10Norm x).val+(boundaryImPowerRow77_7Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree10Norm x).property (boundaryImPowerRow77_7Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree10Norm,boundaryImPowerRow77_7Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x))))=(boundaryImPowerRow77_5Degree10Norm x).val+(boundaryFullPowerDegree10Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree10Norm x).property (boundaryFullPowerDegree10Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree10Norm,boundaryFullPowerDegree10Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))=c} := by

  have he : ((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))=(boundaryImPowerRow77_9Degree10Norm x).val+(boundaryImPowerRow77_10Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree10Norm x).property (boundaryImPowerRow77_10Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree10Norm,boundaryImPowerRow77_10Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))))=(boundaryImPowerRow77_8Degree10Norm x).val+(boundaryFullPowerDegree10Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree10Norm x).property (boundaryFullPowerDegree10Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree10Norm,boundaryFullPowerDegree10Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))))))=(boundaryFullPowerDegree10Block27Norm x).val+(boundaryFullPowerDegree10Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block27Norm x).property (boundaryFullPowerDegree10Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block27Norm,boundaryFullPowerDegree10Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x))))))))=(boundaryFullPowerDegree10Block25Norm x).val+(boundaryFullPowerDegree10Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block25Norm x).property (boundaryFullPowerDegree10Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block25Norm,boundaryFullPowerDegree10Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x))=c} := by

  have he : ((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x))=(boundaryImPowerRow77_12Degree10Norm x).val+(boundaryImPowerRow77_13Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree10Norm x).property (boundaryImPowerRow77_13Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree10Norm,boundaryImPowerRow77_13Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x))))=(boundaryImPowerRow77_11Degree10Norm x).val+(boundaryFullPowerDegree10Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree10Norm x).property (boundaryFullPowerDegree10Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree10Norm,boundaryFullPowerDegree10Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x))=c} := by

  have he : ((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x))=(boundaryImPowerRow77_15Degree10Norm x).val+(boundaryImPowerRow77_16Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree10Norm x).property (boundaryImPowerRow77_16Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree10Norm,boundaryImPowerRow77_16Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x))))=(boundaryImPowerRow77_14Degree10Norm x).val+(boundaryFullPowerDegree10Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree10Norm x).property (boundaryFullPowerDegree10Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree10Norm,boundaryFullPowerDegree10Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x))))))=(boundaryFullPowerDegree10Block33Norm x).val+(boundaryFullPowerDegree10Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block33Norm x).property (boundaryFullPowerDegree10Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block33Norm,boundaryFullPowerDegree10Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x))=c} := by

  have he : ((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x))=(boundaryImPowerRow77_18Degree10Norm x).val+(boundaryImPowerRow77_19Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree10Norm x).property (boundaryImPowerRow77_19Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree10Norm,boundaryImPowerRow77_19Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x))))=(boundaryImPowerRow77_17Degree10Norm x).val+(boundaryFullPowerDegree10Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree10Norm x).property (boundaryFullPowerDegree10Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree10Norm,boundaryFullPowerDegree10Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))=c} := by

  have he : ((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))=(boundaryImPowerRow77_21Degree10Norm x).val+(boundaryLowPowerRow77Degree10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree10Norm x).property (boundaryLowPowerRow77Degree10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree10Norm,boundaryLowPowerRow77Degree10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))=(boundaryImPowerRow77_20Degree10Norm x).val+(boundaryFullPowerDegree10Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree10Norm x).property (boundaryFullPowerDegree10Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree10Norm,boundaryFullPowerDegree10Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))=(boundaryFullPowerDegree10Block38Norm x).val+(boundaryFullPowerDegree10Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block38Norm x).property (boundaryFullPowerDegree10Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block38Norm,boundaryFullPowerDegree10Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))))=(boundaryFullPowerDegree10Block36Norm x).val+(boundaryFullPowerDegree10Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block36Norm x).property (boundaryFullPowerDegree10Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block36Norm,boundaryFullPowerDegree10Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x)))))))))+(((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x)))))))))+(((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))))))=(boundaryFullPowerDegree10Block31Norm x).val+(boundaryFullPowerDegree10Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block31Norm x).property (boundaryFullPowerDegree10Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block31Norm,boundaryFullPowerDegree10Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree10Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x)))))))))+(((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x)))))))))))+(((((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x)))))))))+(((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x)))))))))+(((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x)))))))))))+(((((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x)))))))))+(((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x))))))))))))=(boundaryFullPowerDegree10Block21Norm x).val+(boundaryFullPowerDegree10Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree10Block21Norm x).property (boundaryFullPowerDegree10Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block21Norm,boundaryFullPowerDegree10Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree10Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 10 x=c} := by

  have he0 : boundaryFullPowerRow77 10 x=((((((((((boundaryRePowerRow77_0 10 x)+(boundaryRePowerRow77_1 10 x)))+(((boundaryRePowerRow77_2 10 x)+(((boundaryRePowerRow77_3 10 x)+(boundaryRePowerRow77_4 10 x)))))))+(((((boundaryRePowerRow77_5 10 x)+(((boundaryRePowerRow77_6 10 x)+(boundaryRePowerRow77_7 10 x)))))+(((boundaryRePowerRow77_8 10 x)+(((boundaryRePowerRow77_9 10 x)+(boundaryRePowerRow77_10 10 x)))))))))+(((((((boundaryRePowerRow77_11 10 x)+(((boundaryRePowerRow77_12 10 x)+(boundaryRePowerRow77_13 10 x)))))+(((boundaryRePowerRow77_14 10 x)+(((boundaryRePowerRow77_15 10 x)+(boundaryRePowerRow77_16 10 x)))))))+(((((boundaryRePowerRow77_17 10 x)+(((boundaryRePowerRow77_18 10 x)+(boundaryRePowerRow77_19 10 x)))))+(((boundaryRePowerRow77_20 10 x)+(((boundaryRePowerRow77_21 10 x)+(boundaryRePowerRow77_22 10 x)))))))))))+(((((((((boundaryImPowerRow77_0 10 x)+(boundaryImPowerRow77_1 10 x)))+(((boundaryImPowerRow77_2 10 x)+(((boundaryImPowerRow77_3 10 x)+(boundaryImPowerRow77_4 10 x)))))))+(((((boundaryImPowerRow77_5 10 x)+(((boundaryImPowerRow77_6 10 x)+(boundaryImPowerRow77_7 10 x)))))+(((boundaryImPowerRow77_8 10 x)+(((boundaryImPowerRow77_9 10 x)+(boundaryImPowerRow77_10 10 x)))))))))+(((((((boundaryImPowerRow77_11 10 x)+(((boundaryImPowerRow77_12 10 x)+(boundaryImPowerRow77_13 10 x)))))+(((boundaryImPowerRow77_14 10 x)+(((boundaryImPowerRow77_15 10 x)+(boundaryImPowerRow77_16 10 x)))))))+(((((boundaryImPowerRow77_17 10 x)+(((boundaryImPowerRow77_18 10 x)+(boundaryImPowerRow77_19 10 x)))))+(((boundaryImPowerRow77_20 10 x)+(((boundaryImPowerRow77_21 10 x)+(boundaryLowPowerRow77 10 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree10Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree10Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
