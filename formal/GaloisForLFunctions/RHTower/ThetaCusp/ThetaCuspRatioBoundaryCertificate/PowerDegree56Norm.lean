import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree56Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree56Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x))=c} := by

  have he : ((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x))=(boundaryRePowerRow77_0Degree56Norm x).val+(boundaryRePowerRow77_1Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree56Norm x).property (boundaryRePowerRow77_1Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree56Norm,boundaryRePowerRow77_1Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x))=c} := by

  have he : ((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x))=(boundaryRePowerRow77_3Degree56Norm x).val+(boundaryRePowerRow77_4Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree56Norm x).property (boundaryRePowerRow77_4Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree56Norm,boundaryRePowerRow77_4Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x))))=(boundaryRePowerRow77_2Degree56Norm x).val+(boundaryFullPowerDegree56Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree56Norm x).property (boundaryFullPowerDegree56Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree56Norm,boundaryFullPowerDegree56Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x))))))=(boundaryFullPowerDegree56Block0Norm x).val+(boundaryFullPowerDegree56Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block0Norm x).property (boundaryFullPowerDegree56Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block0Norm,boundaryFullPowerDegree56Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x))=c} := by

  have he : ((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x))=(boundaryRePowerRow77_6Degree56Norm x).val+(boundaryRePowerRow77_7Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree56Norm x).property (boundaryRePowerRow77_7Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree56Norm,boundaryRePowerRow77_7Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x))))=(boundaryRePowerRow77_5Degree56Norm x).val+(boundaryFullPowerDegree56Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree56Norm x).property (boundaryFullPowerDegree56Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree56Norm,boundaryFullPowerDegree56Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))=c} := by

  have he : ((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))=(boundaryRePowerRow77_9Degree56Norm x).val+(boundaryRePowerRow77_10Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree56Norm x).property (boundaryRePowerRow77_10Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree56Norm,boundaryRePowerRow77_10Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))))=(boundaryRePowerRow77_8Degree56Norm x).val+(boundaryFullPowerDegree56Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree56Norm x).property (boundaryFullPowerDegree56Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree56Norm,boundaryFullPowerDegree56Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))))))=(boundaryFullPowerDegree56Block5Norm x).val+(boundaryFullPowerDegree56Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block5Norm x).property (boundaryFullPowerDegree56Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block5Norm,boundaryFullPowerDegree56Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x))))))))=(boundaryFullPowerDegree56Block3Norm x).val+(boundaryFullPowerDegree56Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block3Norm x).property (boundaryFullPowerDegree56Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block3Norm,boundaryFullPowerDegree56Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x))=c} := by

  have he : ((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x))=(boundaryRePowerRow77_12Degree56Norm x).val+(boundaryRePowerRow77_13Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree56Norm x).property (boundaryRePowerRow77_13Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree56Norm,boundaryRePowerRow77_13Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x))))=(boundaryRePowerRow77_11Degree56Norm x).val+(boundaryFullPowerDegree56Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree56Norm x).property (boundaryFullPowerDegree56Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree56Norm,boundaryFullPowerDegree56Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x))=c} := by

  have he : ((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x))=(boundaryRePowerRow77_15Degree56Norm x).val+(boundaryRePowerRow77_16Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree56Norm x).property (boundaryRePowerRow77_16Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree56Norm,boundaryRePowerRow77_16Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x))))=(boundaryRePowerRow77_14Degree56Norm x).val+(boundaryFullPowerDegree56Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree56Norm x).property (boundaryFullPowerDegree56Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree56Norm,boundaryFullPowerDegree56Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x))))))=(boundaryFullPowerDegree56Block11Norm x).val+(boundaryFullPowerDegree56Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block11Norm x).property (boundaryFullPowerDegree56Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block11Norm,boundaryFullPowerDegree56Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x))=c} := by

  have he : ((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x))=(boundaryRePowerRow77_18Degree56Norm x).val+(boundaryRePowerRow77_19Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree56Norm x).property (boundaryRePowerRow77_19Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree56Norm,boundaryRePowerRow77_19Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x))))=(boundaryRePowerRow77_17Degree56Norm x).val+(boundaryFullPowerDegree56Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree56Norm x).property (boundaryFullPowerDegree56Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree56Norm,boundaryFullPowerDegree56Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))=c} := by

  have he : ((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))=(boundaryRePowerRow77_21Degree56Norm x).val+(boundaryRePowerRow77_22Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree56Norm x).property (boundaryRePowerRow77_22Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree56Norm,boundaryRePowerRow77_22Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))=(boundaryRePowerRow77_20Degree56Norm x).val+(boundaryFullPowerDegree56Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree56Norm x).property (boundaryFullPowerDegree56Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree56Norm,boundaryFullPowerDegree56Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))))=(boundaryFullPowerDegree56Block16Norm x).val+(boundaryFullPowerDegree56Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block16Norm x).property (boundaryFullPowerDegree56Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block16Norm,boundaryFullPowerDegree56Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))))))=(boundaryFullPowerDegree56Block14Norm x).val+(boundaryFullPowerDegree56Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block14Norm x).property (boundaryFullPowerDegree56Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block14Norm,boundaryFullPowerDegree56Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x)))))))))+(((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x)))))))))+(((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x))))))))))=(boundaryFullPowerDegree56Block9Norm x).val+(boundaryFullPowerDegree56Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block9Norm x).property (boundaryFullPowerDegree56Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block9Norm,boundaryFullPowerDegree56Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x))=c} := by

  have he : ((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x))=(boundaryImPowerRow77_0Degree56Norm x).val+(boundaryImPowerRow77_1Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree56Norm x).property (boundaryImPowerRow77_1Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree56Norm,boundaryImPowerRow77_1Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x))=c} := by

  have he : ((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x))=(boundaryImPowerRow77_3Degree56Norm x).val+(boundaryImPowerRow77_4Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree56Norm x).property (boundaryImPowerRow77_4Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree56Norm,boundaryImPowerRow77_4Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x))))=(boundaryImPowerRow77_2Degree56Norm x).val+(boundaryFullPowerDegree56Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree56Norm x).property (boundaryFullPowerDegree56Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree56Norm,boundaryFullPowerDegree56Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x))))))=(boundaryFullPowerDegree56Block22Norm x).val+(boundaryFullPowerDegree56Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block22Norm x).property (boundaryFullPowerDegree56Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block22Norm,boundaryFullPowerDegree56Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x))=c} := by

  have he : ((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x))=(boundaryImPowerRow77_6Degree56Norm x).val+(boundaryImPowerRow77_7Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree56Norm x).property (boundaryImPowerRow77_7Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree56Norm,boundaryImPowerRow77_7Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x))))=(boundaryImPowerRow77_5Degree56Norm x).val+(boundaryFullPowerDegree56Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree56Norm x).property (boundaryFullPowerDegree56Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree56Norm,boundaryFullPowerDegree56Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))=c} := by

  have he : ((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))=(boundaryImPowerRow77_9Degree56Norm x).val+(boundaryImPowerRow77_10Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree56Norm x).property (boundaryImPowerRow77_10Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree56Norm,boundaryImPowerRow77_10Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))))=(boundaryImPowerRow77_8Degree56Norm x).val+(boundaryFullPowerDegree56Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree56Norm x).property (boundaryFullPowerDegree56Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree56Norm,boundaryFullPowerDegree56Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))))))=(boundaryFullPowerDegree56Block27Norm x).val+(boundaryFullPowerDegree56Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block27Norm x).property (boundaryFullPowerDegree56Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block27Norm,boundaryFullPowerDegree56Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x))))))))=(boundaryFullPowerDegree56Block25Norm x).val+(boundaryFullPowerDegree56Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block25Norm x).property (boundaryFullPowerDegree56Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block25Norm,boundaryFullPowerDegree56Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x))=c} := by

  have he : ((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x))=(boundaryImPowerRow77_12Degree56Norm x).val+(boundaryImPowerRow77_13Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree56Norm x).property (boundaryImPowerRow77_13Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree56Norm,boundaryImPowerRow77_13Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x))))=(boundaryImPowerRow77_11Degree56Norm x).val+(boundaryFullPowerDegree56Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree56Norm x).property (boundaryFullPowerDegree56Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree56Norm,boundaryFullPowerDegree56Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x))=c} := by

  have he : ((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x))=(boundaryImPowerRow77_15Degree56Norm x).val+(boundaryImPowerRow77_16Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree56Norm x).property (boundaryImPowerRow77_16Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree56Norm,boundaryImPowerRow77_16Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x))))=(boundaryImPowerRow77_14Degree56Norm x).val+(boundaryFullPowerDegree56Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree56Norm x).property (boundaryFullPowerDegree56Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree56Norm,boundaryFullPowerDegree56Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x))))))=(boundaryFullPowerDegree56Block33Norm x).val+(boundaryFullPowerDegree56Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block33Norm x).property (boundaryFullPowerDegree56Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block33Norm,boundaryFullPowerDegree56Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x))=c} := by

  have he : ((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x))=(boundaryImPowerRow77_18Degree56Norm x).val+(boundaryImPowerRow77_19Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree56Norm x).property (boundaryImPowerRow77_19Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree56Norm,boundaryImPowerRow77_19Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x))))=(boundaryImPowerRow77_17Degree56Norm x).val+(boundaryFullPowerDegree56Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree56Norm x).property (boundaryFullPowerDegree56Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree56Norm,boundaryFullPowerDegree56Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))=c} := by

  have he : ((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))=(boundaryImPowerRow77_21Degree56Norm x).val+(boundaryLowPowerRow77Degree56Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree56Norm x).property (boundaryLowPowerRow77Degree56Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree56Norm,boundaryLowPowerRow77Degree56Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))=(boundaryImPowerRow77_20Degree56Norm x).val+(boundaryFullPowerDegree56Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree56Norm x).property (boundaryFullPowerDegree56Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree56Norm,boundaryFullPowerDegree56Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))=(boundaryFullPowerDegree56Block38Norm x).val+(boundaryFullPowerDegree56Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block38Norm x).property (boundaryFullPowerDegree56Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block38Norm,boundaryFullPowerDegree56Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))))=(boundaryFullPowerDegree56Block36Norm x).val+(boundaryFullPowerDegree56Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block36Norm x).property (boundaryFullPowerDegree56Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block36Norm,boundaryFullPowerDegree56Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x)))))))))+(((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x)))))))))+(((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))))))=(boundaryFullPowerDegree56Block31Norm x).val+(boundaryFullPowerDegree56Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block31Norm x).property (boundaryFullPowerDegree56Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block31Norm,boundaryFullPowerDegree56Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree56Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x)))))))))+(((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x)))))))))))+(((((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x)))))))))+(((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x)))))))))+(((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x)))))))))))+(((((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x)))))))))+(((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x))))))))))))=(boundaryFullPowerDegree56Block21Norm x).val+(boundaryFullPowerDegree56Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree56Block21Norm x).property (boundaryFullPowerDegree56Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block21Norm,boundaryFullPowerDegree56Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree56Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 56 x=c} := by

  have he0 : boundaryFullPowerRow77 56 x=((((((((((boundaryRePowerRow77_0 56 x)+(boundaryRePowerRow77_1 56 x)))+(((boundaryRePowerRow77_2 56 x)+(((boundaryRePowerRow77_3 56 x)+(boundaryRePowerRow77_4 56 x)))))))+(((((boundaryRePowerRow77_5 56 x)+(((boundaryRePowerRow77_6 56 x)+(boundaryRePowerRow77_7 56 x)))))+(((boundaryRePowerRow77_8 56 x)+(((boundaryRePowerRow77_9 56 x)+(boundaryRePowerRow77_10 56 x)))))))))+(((((((boundaryRePowerRow77_11 56 x)+(((boundaryRePowerRow77_12 56 x)+(boundaryRePowerRow77_13 56 x)))))+(((boundaryRePowerRow77_14 56 x)+(((boundaryRePowerRow77_15 56 x)+(boundaryRePowerRow77_16 56 x)))))))+(((((boundaryRePowerRow77_17 56 x)+(((boundaryRePowerRow77_18 56 x)+(boundaryRePowerRow77_19 56 x)))))+(((boundaryRePowerRow77_20 56 x)+(((boundaryRePowerRow77_21 56 x)+(boundaryRePowerRow77_22 56 x)))))))))))+(((((((((boundaryImPowerRow77_0 56 x)+(boundaryImPowerRow77_1 56 x)))+(((boundaryImPowerRow77_2 56 x)+(((boundaryImPowerRow77_3 56 x)+(boundaryImPowerRow77_4 56 x)))))))+(((((boundaryImPowerRow77_5 56 x)+(((boundaryImPowerRow77_6 56 x)+(boundaryImPowerRow77_7 56 x)))))+(((boundaryImPowerRow77_8 56 x)+(((boundaryImPowerRow77_9 56 x)+(boundaryImPowerRow77_10 56 x)))))))))+(((((((boundaryImPowerRow77_11 56 x)+(((boundaryImPowerRow77_12 56 x)+(boundaryImPowerRow77_13 56 x)))))+(((boundaryImPowerRow77_14 56 x)+(((boundaryImPowerRow77_15 56 x)+(boundaryImPowerRow77_16 56 x)))))))+(((((boundaryImPowerRow77_17 56 x)+(((boundaryImPowerRow77_18 56 x)+(boundaryImPowerRow77_19 56 x)))))+(((boundaryImPowerRow77_20 56 x)+(((boundaryImPowerRow77_21 56 x)+(boundaryLowPowerRow77 56 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree56Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree56Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
