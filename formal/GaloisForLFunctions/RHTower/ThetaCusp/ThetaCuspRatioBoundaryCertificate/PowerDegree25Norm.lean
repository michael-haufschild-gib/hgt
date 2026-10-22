import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree25Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree25Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x))=c} := by

  have he : ((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x))=(boundaryRePowerRow77_0Degree25Norm x).val+(boundaryRePowerRow77_1Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree25Norm x).property (boundaryRePowerRow77_1Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree25Norm,boundaryRePowerRow77_1Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x))=c} := by

  have he : ((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x))=(boundaryRePowerRow77_3Degree25Norm x).val+(boundaryRePowerRow77_4Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree25Norm x).property (boundaryRePowerRow77_4Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree25Norm,boundaryRePowerRow77_4Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x))))=(boundaryRePowerRow77_2Degree25Norm x).val+(boundaryFullPowerDegree25Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree25Norm x).property (boundaryFullPowerDegree25Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree25Norm,boundaryFullPowerDegree25Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x))))))=(boundaryFullPowerDegree25Block0Norm x).val+(boundaryFullPowerDegree25Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block0Norm x).property (boundaryFullPowerDegree25Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block0Norm,boundaryFullPowerDegree25Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x))=c} := by

  have he : ((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x))=(boundaryRePowerRow77_6Degree25Norm x).val+(boundaryRePowerRow77_7Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree25Norm x).property (boundaryRePowerRow77_7Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree25Norm,boundaryRePowerRow77_7Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x))))=(boundaryRePowerRow77_5Degree25Norm x).val+(boundaryFullPowerDegree25Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree25Norm x).property (boundaryFullPowerDegree25Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree25Norm,boundaryFullPowerDegree25Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))=c} := by

  have he : ((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))=(boundaryRePowerRow77_9Degree25Norm x).val+(boundaryRePowerRow77_10Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree25Norm x).property (boundaryRePowerRow77_10Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree25Norm,boundaryRePowerRow77_10Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))))=(boundaryRePowerRow77_8Degree25Norm x).val+(boundaryFullPowerDegree25Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree25Norm x).property (boundaryFullPowerDegree25Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree25Norm,boundaryFullPowerDegree25Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))))))=(boundaryFullPowerDegree25Block5Norm x).val+(boundaryFullPowerDegree25Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block5Norm x).property (boundaryFullPowerDegree25Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block5Norm,boundaryFullPowerDegree25Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x))))))))=(boundaryFullPowerDegree25Block3Norm x).val+(boundaryFullPowerDegree25Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block3Norm x).property (boundaryFullPowerDegree25Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block3Norm,boundaryFullPowerDegree25Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x))=c} := by

  have he : ((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x))=(boundaryRePowerRow77_12Degree25Norm x).val+(boundaryRePowerRow77_13Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree25Norm x).property (boundaryRePowerRow77_13Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree25Norm,boundaryRePowerRow77_13Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x))))=(boundaryRePowerRow77_11Degree25Norm x).val+(boundaryFullPowerDegree25Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree25Norm x).property (boundaryFullPowerDegree25Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree25Norm,boundaryFullPowerDegree25Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x))=c} := by

  have he : ((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x))=(boundaryRePowerRow77_15Degree25Norm x).val+(boundaryRePowerRow77_16Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree25Norm x).property (boundaryRePowerRow77_16Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree25Norm,boundaryRePowerRow77_16Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x))))=(boundaryRePowerRow77_14Degree25Norm x).val+(boundaryFullPowerDegree25Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree25Norm x).property (boundaryFullPowerDegree25Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree25Norm,boundaryFullPowerDegree25Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x))))))=(boundaryFullPowerDegree25Block11Norm x).val+(boundaryFullPowerDegree25Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block11Norm x).property (boundaryFullPowerDegree25Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block11Norm,boundaryFullPowerDegree25Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x))=c} := by

  have he : ((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x))=(boundaryRePowerRow77_18Degree25Norm x).val+(boundaryRePowerRow77_19Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree25Norm x).property (boundaryRePowerRow77_19Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree25Norm,boundaryRePowerRow77_19Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x))))=(boundaryRePowerRow77_17Degree25Norm x).val+(boundaryFullPowerDegree25Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree25Norm x).property (boundaryFullPowerDegree25Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree25Norm,boundaryFullPowerDegree25Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))=c} := by

  have he : ((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))=(boundaryRePowerRow77_21Degree25Norm x).val+(boundaryRePowerRow77_22Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree25Norm x).property (boundaryRePowerRow77_22Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree25Norm,boundaryRePowerRow77_22Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))=(boundaryRePowerRow77_20Degree25Norm x).val+(boundaryFullPowerDegree25Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree25Norm x).property (boundaryFullPowerDegree25Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree25Norm,boundaryFullPowerDegree25Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))))=(boundaryFullPowerDegree25Block16Norm x).val+(boundaryFullPowerDegree25Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block16Norm x).property (boundaryFullPowerDegree25Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block16Norm,boundaryFullPowerDegree25Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))))))=(boundaryFullPowerDegree25Block14Norm x).val+(boundaryFullPowerDegree25Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block14Norm x).property (boundaryFullPowerDegree25Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block14Norm,boundaryFullPowerDegree25Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x)))))))))+(((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x)))))))))+(((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x))))))))))=(boundaryFullPowerDegree25Block9Norm x).val+(boundaryFullPowerDegree25Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block9Norm x).property (boundaryFullPowerDegree25Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block9Norm,boundaryFullPowerDegree25Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x))=c} := by

  have he : ((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x))=(boundaryImPowerRow77_0Degree25Norm x).val+(boundaryImPowerRow77_1Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree25Norm x).property (boundaryImPowerRow77_1Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree25Norm,boundaryImPowerRow77_1Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x))=c} := by

  have he : ((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x))=(boundaryImPowerRow77_3Degree25Norm x).val+(boundaryImPowerRow77_4Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree25Norm x).property (boundaryImPowerRow77_4Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree25Norm,boundaryImPowerRow77_4Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x))))=(boundaryImPowerRow77_2Degree25Norm x).val+(boundaryFullPowerDegree25Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree25Norm x).property (boundaryFullPowerDegree25Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree25Norm,boundaryFullPowerDegree25Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x))))))=(boundaryFullPowerDegree25Block22Norm x).val+(boundaryFullPowerDegree25Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block22Norm x).property (boundaryFullPowerDegree25Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block22Norm,boundaryFullPowerDegree25Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x))=c} := by

  have he : ((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x))=(boundaryImPowerRow77_6Degree25Norm x).val+(boundaryImPowerRow77_7Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree25Norm x).property (boundaryImPowerRow77_7Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree25Norm,boundaryImPowerRow77_7Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x))))=(boundaryImPowerRow77_5Degree25Norm x).val+(boundaryFullPowerDegree25Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree25Norm x).property (boundaryFullPowerDegree25Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree25Norm,boundaryFullPowerDegree25Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))=c} := by

  have he : ((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))=(boundaryImPowerRow77_9Degree25Norm x).val+(boundaryImPowerRow77_10Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree25Norm x).property (boundaryImPowerRow77_10Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree25Norm,boundaryImPowerRow77_10Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))))=(boundaryImPowerRow77_8Degree25Norm x).val+(boundaryFullPowerDegree25Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree25Norm x).property (boundaryFullPowerDegree25Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree25Norm,boundaryFullPowerDegree25Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))))))=(boundaryFullPowerDegree25Block27Norm x).val+(boundaryFullPowerDegree25Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block27Norm x).property (boundaryFullPowerDegree25Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block27Norm,boundaryFullPowerDegree25Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x))))))))=(boundaryFullPowerDegree25Block25Norm x).val+(boundaryFullPowerDegree25Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block25Norm x).property (boundaryFullPowerDegree25Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block25Norm,boundaryFullPowerDegree25Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x))=c} := by

  have he : ((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x))=(boundaryImPowerRow77_12Degree25Norm x).val+(boundaryImPowerRow77_13Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree25Norm x).property (boundaryImPowerRow77_13Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree25Norm,boundaryImPowerRow77_13Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x))))=(boundaryImPowerRow77_11Degree25Norm x).val+(boundaryFullPowerDegree25Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree25Norm x).property (boundaryFullPowerDegree25Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree25Norm,boundaryFullPowerDegree25Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x))=c} := by

  have he : ((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x))=(boundaryImPowerRow77_15Degree25Norm x).val+(boundaryImPowerRow77_16Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree25Norm x).property (boundaryImPowerRow77_16Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree25Norm,boundaryImPowerRow77_16Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x))))=(boundaryImPowerRow77_14Degree25Norm x).val+(boundaryFullPowerDegree25Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree25Norm x).property (boundaryFullPowerDegree25Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree25Norm,boundaryFullPowerDegree25Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x))))))=(boundaryFullPowerDegree25Block33Norm x).val+(boundaryFullPowerDegree25Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block33Norm x).property (boundaryFullPowerDegree25Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block33Norm,boundaryFullPowerDegree25Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x))=c} := by

  have he : ((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x))=(boundaryImPowerRow77_18Degree25Norm x).val+(boundaryImPowerRow77_19Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree25Norm x).property (boundaryImPowerRow77_19Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree25Norm,boundaryImPowerRow77_19Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x))))=(boundaryImPowerRow77_17Degree25Norm x).val+(boundaryFullPowerDegree25Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree25Norm x).property (boundaryFullPowerDegree25Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree25Norm,boundaryFullPowerDegree25Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))=c} := by

  have he : ((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))=(boundaryImPowerRow77_21Degree25Norm x).val+(boundaryLowPowerRow77Degree25Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree25Norm x).property (boundaryLowPowerRow77Degree25Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree25Norm,boundaryLowPowerRow77Degree25Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))=(boundaryImPowerRow77_20Degree25Norm x).val+(boundaryFullPowerDegree25Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree25Norm x).property (boundaryFullPowerDegree25Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree25Norm,boundaryFullPowerDegree25Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))=(boundaryFullPowerDegree25Block38Norm x).val+(boundaryFullPowerDegree25Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block38Norm x).property (boundaryFullPowerDegree25Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block38Norm,boundaryFullPowerDegree25Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))))=(boundaryFullPowerDegree25Block36Norm x).val+(boundaryFullPowerDegree25Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block36Norm x).property (boundaryFullPowerDegree25Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block36Norm,boundaryFullPowerDegree25Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x)))))))))+(((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x)))))))))+(((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))))))=(boundaryFullPowerDegree25Block31Norm x).val+(boundaryFullPowerDegree25Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block31Norm x).property (boundaryFullPowerDegree25Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block31Norm,boundaryFullPowerDegree25Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree25Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x)))))))))+(((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x)))))))))))+(((((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x)))))))))+(((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x)))))))))+(((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x)))))))))))+(((((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x)))))))))+(((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x))))))))))))=(boundaryFullPowerDegree25Block21Norm x).val+(boundaryFullPowerDegree25Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree25Block21Norm x).property (boundaryFullPowerDegree25Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block21Norm,boundaryFullPowerDegree25Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree25Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 25 x=c} := by

  have he0 : boundaryFullPowerRow77 25 x=((((((((((boundaryRePowerRow77_0 25 x)+(boundaryRePowerRow77_1 25 x)))+(((boundaryRePowerRow77_2 25 x)+(((boundaryRePowerRow77_3 25 x)+(boundaryRePowerRow77_4 25 x)))))))+(((((boundaryRePowerRow77_5 25 x)+(((boundaryRePowerRow77_6 25 x)+(boundaryRePowerRow77_7 25 x)))))+(((boundaryRePowerRow77_8 25 x)+(((boundaryRePowerRow77_9 25 x)+(boundaryRePowerRow77_10 25 x)))))))))+(((((((boundaryRePowerRow77_11 25 x)+(((boundaryRePowerRow77_12 25 x)+(boundaryRePowerRow77_13 25 x)))))+(((boundaryRePowerRow77_14 25 x)+(((boundaryRePowerRow77_15 25 x)+(boundaryRePowerRow77_16 25 x)))))))+(((((boundaryRePowerRow77_17 25 x)+(((boundaryRePowerRow77_18 25 x)+(boundaryRePowerRow77_19 25 x)))))+(((boundaryRePowerRow77_20 25 x)+(((boundaryRePowerRow77_21 25 x)+(boundaryRePowerRow77_22 25 x)))))))))))+(((((((((boundaryImPowerRow77_0 25 x)+(boundaryImPowerRow77_1 25 x)))+(((boundaryImPowerRow77_2 25 x)+(((boundaryImPowerRow77_3 25 x)+(boundaryImPowerRow77_4 25 x)))))))+(((((boundaryImPowerRow77_5 25 x)+(((boundaryImPowerRow77_6 25 x)+(boundaryImPowerRow77_7 25 x)))))+(((boundaryImPowerRow77_8 25 x)+(((boundaryImPowerRow77_9 25 x)+(boundaryImPowerRow77_10 25 x)))))))))+(((((((boundaryImPowerRow77_11 25 x)+(((boundaryImPowerRow77_12 25 x)+(boundaryImPowerRow77_13 25 x)))))+(((boundaryImPowerRow77_14 25 x)+(((boundaryImPowerRow77_15 25 x)+(boundaryImPowerRow77_16 25 x)))))))+(((((boundaryImPowerRow77_17 25 x)+(((boundaryImPowerRow77_18 25 x)+(boundaryImPowerRow77_19 25 x)))))+(((boundaryImPowerRow77_20 25 x)+(((boundaryImPowerRow77_21 25 x)+(boundaryLowPowerRow77 25 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree25Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree25Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
