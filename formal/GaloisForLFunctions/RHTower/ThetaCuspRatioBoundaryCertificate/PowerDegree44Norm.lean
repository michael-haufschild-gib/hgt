import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree44Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree44Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x))=c} := by

  have he : ((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x))=(boundaryRePowerRow77_0Degree44Norm x).val+(boundaryRePowerRow77_1Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree44Norm x).property (boundaryRePowerRow77_1Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree44Norm,boundaryRePowerRow77_1Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x))=c} := by

  have he : ((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x))=(boundaryRePowerRow77_3Degree44Norm x).val+(boundaryRePowerRow77_4Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree44Norm x).property (boundaryRePowerRow77_4Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree44Norm,boundaryRePowerRow77_4Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x))))=(boundaryRePowerRow77_2Degree44Norm x).val+(boundaryFullPowerDegree44Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree44Norm x).property (boundaryFullPowerDegree44Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree44Norm,boundaryFullPowerDegree44Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x))))))=(boundaryFullPowerDegree44Block0Norm x).val+(boundaryFullPowerDegree44Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block0Norm x).property (boundaryFullPowerDegree44Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block0Norm,boundaryFullPowerDegree44Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x))=c} := by

  have he : ((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x))=(boundaryRePowerRow77_6Degree44Norm x).val+(boundaryRePowerRow77_7Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree44Norm x).property (boundaryRePowerRow77_7Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree44Norm,boundaryRePowerRow77_7Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x))))=(boundaryRePowerRow77_5Degree44Norm x).val+(boundaryFullPowerDegree44Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree44Norm x).property (boundaryFullPowerDegree44Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree44Norm,boundaryFullPowerDegree44Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))=c} := by

  have he : ((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))=(boundaryRePowerRow77_9Degree44Norm x).val+(boundaryRePowerRow77_10Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree44Norm x).property (boundaryRePowerRow77_10Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree44Norm,boundaryRePowerRow77_10Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))))=(boundaryRePowerRow77_8Degree44Norm x).val+(boundaryFullPowerDegree44Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree44Norm x).property (boundaryFullPowerDegree44Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree44Norm,boundaryFullPowerDegree44Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))))))=(boundaryFullPowerDegree44Block5Norm x).val+(boundaryFullPowerDegree44Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block5Norm x).property (boundaryFullPowerDegree44Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block5Norm,boundaryFullPowerDegree44Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x))))))))=(boundaryFullPowerDegree44Block3Norm x).val+(boundaryFullPowerDegree44Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block3Norm x).property (boundaryFullPowerDegree44Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block3Norm,boundaryFullPowerDegree44Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x))=c} := by

  have he : ((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x))=(boundaryRePowerRow77_12Degree44Norm x).val+(boundaryRePowerRow77_13Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree44Norm x).property (boundaryRePowerRow77_13Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree44Norm,boundaryRePowerRow77_13Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x))))=(boundaryRePowerRow77_11Degree44Norm x).val+(boundaryFullPowerDegree44Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree44Norm x).property (boundaryFullPowerDegree44Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree44Norm,boundaryFullPowerDegree44Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x))=c} := by

  have he : ((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x))=(boundaryRePowerRow77_15Degree44Norm x).val+(boundaryRePowerRow77_16Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree44Norm x).property (boundaryRePowerRow77_16Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree44Norm,boundaryRePowerRow77_16Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x))))=(boundaryRePowerRow77_14Degree44Norm x).val+(boundaryFullPowerDegree44Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree44Norm x).property (boundaryFullPowerDegree44Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree44Norm,boundaryFullPowerDegree44Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x))))))=(boundaryFullPowerDegree44Block11Norm x).val+(boundaryFullPowerDegree44Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block11Norm x).property (boundaryFullPowerDegree44Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block11Norm,boundaryFullPowerDegree44Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x))=c} := by

  have he : ((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x))=(boundaryRePowerRow77_18Degree44Norm x).val+(boundaryRePowerRow77_19Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree44Norm x).property (boundaryRePowerRow77_19Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree44Norm,boundaryRePowerRow77_19Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x))))=(boundaryRePowerRow77_17Degree44Norm x).val+(boundaryFullPowerDegree44Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree44Norm x).property (boundaryFullPowerDegree44Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree44Norm,boundaryFullPowerDegree44Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))=c} := by

  have he : ((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))=(boundaryRePowerRow77_21Degree44Norm x).val+(boundaryRePowerRow77_22Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree44Norm x).property (boundaryRePowerRow77_22Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree44Norm,boundaryRePowerRow77_22Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))=(boundaryRePowerRow77_20Degree44Norm x).val+(boundaryFullPowerDegree44Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree44Norm x).property (boundaryFullPowerDegree44Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree44Norm,boundaryFullPowerDegree44Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))))=(boundaryFullPowerDegree44Block16Norm x).val+(boundaryFullPowerDegree44Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block16Norm x).property (boundaryFullPowerDegree44Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block16Norm,boundaryFullPowerDegree44Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))))))=(boundaryFullPowerDegree44Block14Norm x).val+(boundaryFullPowerDegree44Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block14Norm x).property (boundaryFullPowerDegree44Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block14Norm,boundaryFullPowerDegree44Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x)))))))))+(((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x)))))))))+(((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x))))))))))=(boundaryFullPowerDegree44Block9Norm x).val+(boundaryFullPowerDegree44Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block9Norm x).property (boundaryFullPowerDegree44Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block9Norm,boundaryFullPowerDegree44Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x))=c} := by

  have he : ((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x))=(boundaryImPowerRow77_0Degree44Norm x).val+(boundaryImPowerRow77_1Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree44Norm x).property (boundaryImPowerRow77_1Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree44Norm,boundaryImPowerRow77_1Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x))=c} := by

  have he : ((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x))=(boundaryImPowerRow77_3Degree44Norm x).val+(boundaryImPowerRow77_4Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree44Norm x).property (boundaryImPowerRow77_4Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree44Norm,boundaryImPowerRow77_4Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x))))=(boundaryImPowerRow77_2Degree44Norm x).val+(boundaryFullPowerDegree44Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree44Norm x).property (boundaryFullPowerDegree44Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree44Norm,boundaryFullPowerDegree44Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x))))))=(boundaryFullPowerDegree44Block22Norm x).val+(boundaryFullPowerDegree44Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block22Norm x).property (boundaryFullPowerDegree44Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block22Norm,boundaryFullPowerDegree44Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x))=c} := by

  have he : ((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x))=(boundaryImPowerRow77_6Degree44Norm x).val+(boundaryImPowerRow77_7Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree44Norm x).property (boundaryImPowerRow77_7Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree44Norm,boundaryImPowerRow77_7Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x))))=(boundaryImPowerRow77_5Degree44Norm x).val+(boundaryFullPowerDegree44Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree44Norm x).property (boundaryFullPowerDegree44Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree44Norm,boundaryFullPowerDegree44Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))=c} := by

  have he : ((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))=(boundaryImPowerRow77_9Degree44Norm x).val+(boundaryImPowerRow77_10Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree44Norm x).property (boundaryImPowerRow77_10Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree44Norm,boundaryImPowerRow77_10Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))))=(boundaryImPowerRow77_8Degree44Norm x).val+(boundaryFullPowerDegree44Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree44Norm x).property (boundaryFullPowerDegree44Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree44Norm,boundaryFullPowerDegree44Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))))))=(boundaryFullPowerDegree44Block27Norm x).val+(boundaryFullPowerDegree44Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block27Norm x).property (boundaryFullPowerDegree44Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block27Norm,boundaryFullPowerDegree44Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x))))))))=(boundaryFullPowerDegree44Block25Norm x).val+(boundaryFullPowerDegree44Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block25Norm x).property (boundaryFullPowerDegree44Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block25Norm,boundaryFullPowerDegree44Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x))=c} := by

  have he : ((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x))=(boundaryImPowerRow77_12Degree44Norm x).val+(boundaryImPowerRow77_13Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree44Norm x).property (boundaryImPowerRow77_13Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree44Norm,boundaryImPowerRow77_13Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x))))=(boundaryImPowerRow77_11Degree44Norm x).val+(boundaryFullPowerDegree44Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree44Norm x).property (boundaryFullPowerDegree44Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree44Norm,boundaryFullPowerDegree44Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x))=c} := by

  have he : ((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x))=(boundaryImPowerRow77_15Degree44Norm x).val+(boundaryImPowerRow77_16Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree44Norm x).property (boundaryImPowerRow77_16Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree44Norm,boundaryImPowerRow77_16Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x))))=(boundaryImPowerRow77_14Degree44Norm x).val+(boundaryFullPowerDegree44Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree44Norm x).property (boundaryFullPowerDegree44Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree44Norm,boundaryFullPowerDegree44Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x))))))=(boundaryFullPowerDegree44Block33Norm x).val+(boundaryFullPowerDegree44Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block33Norm x).property (boundaryFullPowerDegree44Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block33Norm,boundaryFullPowerDegree44Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x))=c} := by

  have he : ((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x))=(boundaryImPowerRow77_18Degree44Norm x).val+(boundaryImPowerRow77_19Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree44Norm x).property (boundaryImPowerRow77_19Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree44Norm,boundaryImPowerRow77_19Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x))))=(boundaryImPowerRow77_17Degree44Norm x).val+(boundaryFullPowerDegree44Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree44Norm x).property (boundaryFullPowerDegree44Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree44Norm,boundaryFullPowerDegree44Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))=c} := by

  have he : ((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))=(boundaryImPowerRow77_21Degree44Norm x).val+(boundaryLowPowerRow77Degree44Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree44Norm x).property (boundaryLowPowerRow77Degree44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree44Norm,boundaryLowPowerRow77Degree44Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))=(boundaryImPowerRow77_20Degree44Norm x).val+(boundaryFullPowerDegree44Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree44Norm x).property (boundaryFullPowerDegree44Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree44Norm,boundaryFullPowerDegree44Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))=(boundaryFullPowerDegree44Block38Norm x).val+(boundaryFullPowerDegree44Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block38Norm x).property (boundaryFullPowerDegree44Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block38Norm,boundaryFullPowerDegree44Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))))=(boundaryFullPowerDegree44Block36Norm x).val+(boundaryFullPowerDegree44Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block36Norm x).property (boundaryFullPowerDegree44Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block36Norm,boundaryFullPowerDegree44Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x)))))))))+(((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x)))))))))+(((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))))))=(boundaryFullPowerDegree44Block31Norm x).val+(boundaryFullPowerDegree44Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block31Norm x).property (boundaryFullPowerDegree44Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block31Norm,boundaryFullPowerDegree44Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree44Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x)))))))))+(((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x)))))))))))+(((((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x)))))))))+(((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x)))))))))+(((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x)))))))))))+(((((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x)))))))))+(((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x))))))))))))=(boundaryFullPowerDegree44Block21Norm x).val+(boundaryFullPowerDegree44Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree44Block21Norm x).property (boundaryFullPowerDegree44Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block21Norm,boundaryFullPowerDegree44Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree44Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 44 x=c} := by

  have he0 : boundaryFullPowerRow77 44 x=((((((((((boundaryRePowerRow77_0 44 x)+(boundaryRePowerRow77_1 44 x)))+(((boundaryRePowerRow77_2 44 x)+(((boundaryRePowerRow77_3 44 x)+(boundaryRePowerRow77_4 44 x)))))))+(((((boundaryRePowerRow77_5 44 x)+(((boundaryRePowerRow77_6 44 x)+(boundaryRePowerRow77_7 44 x)))))+(((boundaryRePowerRow77_8 44 x)+(((boundaryRePowerRow77_9 44 x)+(boundaryRePowerRow77_10 44 x)))))))))+(((((((boundaryRePowerRow77_11 44 x)+(((boundaryRePowerRow77_12 44 x)+(boundaryRePowerRow77_13 44 x)))))+(((boundaryRePowerRow77_14 44 x)+(((boundaryRePowerRow77_15 44 x)+(boundaryRePowerRow77_16 44 x)))))))+(((((boundaryRePowerRow77_17 44 x)+(((boundaryRePowerRow77_18 44 x)+(boundaryRePowerRow77_19 44 x)))))+(((boundaryRePowerRow77_20 44 x)+(((boundaryRePowerRow77_21 44 x)+(boundaryRePowerRow77_22 44 x)))))))))))+(((((((((boundaryImPowerRow77_0 44 x)+(boundaryImPowerRow77_1 44 x)))+(((boundaryImPowerRow77_2 44 x)+(((boundaryImPowerRow77_3 44 x)+(boundaryImPowerRow77_4 44 x)))))))+(((((boundaryImPowerRow77_5 44 x)+(((boundaryImPowerRow77_6 44 x)+(boundaryImPowerRow77_7 44 x)))))+(((boundaryImPowerRow77_8 44 x)+(((boundaryImPowerRow77_9 44 x)+(boundaryImPowerRow77_10 44 x)))))))))+(((((((boundaryImPowerRow77_11 44 x)+(((boundaryImPowerRow77_12 44 x)+(boundaryImPowerRow77_13 44 x)))))+(((boundaryImPowerRow77_14 44 x)+(((boundaryImPowerRow77_15 44 x)+(boundaryImPowerRow77_16 44 x)))))))+(((((boundaryImPowerRow77_17 44 x)+(((boundaryImPowerRow77_18 44 x)+(boundaryImPowerRow77_19 44 x)))))+(((boundaryImPowerRow77_20 44 x)+(((boundaryImPowerRow77_21 44 x)+(boundaryLowPowerRow77 44 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree44Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree44Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
