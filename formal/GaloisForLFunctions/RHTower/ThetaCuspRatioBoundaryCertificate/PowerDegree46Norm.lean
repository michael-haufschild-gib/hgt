import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree46Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree46Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x))=c} := by

  have he : ((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x))=(boundaryRePowerRow77_0Degree46Norm x).val+(boundaryRePowerRow77_1Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree46Norm x).property (boundaryRePowerRow77_1Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree46Norm,boundaryRePowerRow77_1Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x))=c} := by

  have he : ((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x))=(boundaryRePowerRow77_3Degree46Norm x).val+(boundaryRePowerRow77_4Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree46Norm x).property (boundaryRePowerRow77_4Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree46Norm,boundaryRePowerRow77_4Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x))))=(boundaryRePowerRow77_2Degree46Norm x).val+(boundaryFullPowerDegree46Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree46Norm x).property (boundaryFullPowerDegree46Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree46Norm,boundaryFullPowerDegree46Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x))))))=(boundaryFullPowerDegree46Block0Norm x).val+(boundaryFullPowerDegree46Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block0Norm x).property (boundaryFullPowerDegree46Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block0Norm,boundaryFullPowerDegree46Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x))=c} := by

  have he : ((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x))=(boundaryRePowerRow77_6Degree46Norm x).val+(boundaryRePowerRow77_7Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree46Norm x).property (boundaryRePowerRow77_7Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree46Norm,boundaryRePowerRow77_7Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x))))=(boundaryRePowerRow77_5Degree46Norm x).val+(boundaryFullPowerDegree46Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree46Norm x).property (boundaryFullPowerDegree46Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree46Norm,boundaryFullPowerDegree46Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))=c} := by

  have he : ((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))=(boundaryRePowerRow77_9Degree46Norm x).val+(boundaryRePowerRow77_10Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree46Norm x).property (boundaryRePowerRow77_10Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree46Norm,boundaryRePowerRow77_10Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))))=(boundaryRePowerRow77_8Degree46Norm x).val+(boundaryFullPowerDegree46Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree46Norm x).property (boundaryFullPowerDegree46Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree46Norm,boundaryFullPowerDegree46Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))))))=(boundaryFullPowerDegree46Block5Norm x).val+(boundaryFullPowerDegree46Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block5Norm x).property (boundaryFullPowerDegree46Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block5Norm,boundaryFullPowerDegree46Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x))))))))=(boundaryFullPowerDegree46Block3Norm x).val+(boundaryFullPowerDegree46Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block3Norm x).property (boundaryFullPowerDegree46Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block3Norm,boundaryFullPowerDegree46Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x))=c} := by

  have he : ((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x))=(boundaryRePowerRow77_12Degree46Norm x).val+(boundaryRePowerRow77_13Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree46Norm x).property (boundaryRePowerRow77_13Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree46Norm,boundaryRePowerRow77_13Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x))))=(boundaryRePowerRow77_11Degree46Norm x).val+(boundaryFullPowerDegree46Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree46Norm x).property (boundaryFullPowerDegree46Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree46Norm,boundaryFullPowerDegree46Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x))=c} := by

  have he : ((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x))=(boundaryRePowerRow77_15Degree46Norm x).val+(boundaryRePowerRow77_16Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree46Norm x).property (boundaryRePowerRow77_16Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree46Norm,boundaryRePowerRow77_16Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x))))=(boundaryRePowerRow77_14Degree46Norm x).val+(boundaryFullPowerDegree46Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree46Norm x).property (boundaryFullPowerDegree46Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree46Norm,boundaryFullPowerDegree46Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x))))))=(boundaryFullPowerDegree46Block11Norm x).val+(boundaryFullPowerDegree46Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block11Norm x).property (boundaryFullPowerDegree46Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block11Norm,boundaryFullPowerDegree46Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x))=c} := by

  have he : ((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x))=(boundaryRePowerRow77_18Degree46Norm x).val+(boundaryRePowerRow77_19Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree46Norm x).property (boundaryRePowerRow77_19Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree46Norm,boundaryRePowerRow77_19Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x))))=(boundaryRePowerRow77_17Degree46Norm x).val+(boundaryFullPowerDegree46Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree46Norm x).property (boundaryFullPowerDegree46Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree46Norm,boundaryFullPowerDegree46Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))=c} := by

  have he : ((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))=(boundaryRePowerRow77_21Degree46Norm x).val+(boundaryRePowerRow77_22Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree46Norm x).property (boundaryRePowerRow77_22Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree46Norm,boundaryRePowerRow77_22Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))=(boundaryRePowerRow77_20Degree46Norm x).val+(boundaryFullPowerDegree46Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree46Norm x).property (boundaryFullPowerDegree46Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree46Norm,boundaryFullPowerDegree46Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))))=(boundaryFullPowerDegree46Block16Norm x).val+(boundaryFullPowerDegree46Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block16Norm x).property (boundaryFullPowerDegree46Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block16Norm,boundaryFullPowerDegree46Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))))))=(boundaryFullPowerDegree46Block14Norm x).val+(boundaryFullPowerDegree46Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block14Norm x).property (boundaryFullPowerDegree46Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block14Norm,boundaryFullPowerDegree46Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x)))))))))+(((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x)))))))))+(((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x))))))))))=(boundaryFullPowerDegree46Block9Norm x).val+(boundaryFullPowerDegree46Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block9Norm x).property (boundaryFullPowerDegree46Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block9Norm,boundaryFullPowerDegree46Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x))=c} := by

  have he : ((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x))=(boundaryImPowerRow77_0Degree46Norm x).val+(boundaryImPowerRow77_1Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree46Norm x).property (boundaryImPowerRow77_1Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree46Norm,boundaryImPowerRow77_1Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x))=c} := by

  have he : ((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x))=(boundaryImPowerRow77_3Degree46Norm x).val+(boundaryImPowerRow77_4Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree46Norm x).property (boundaryImPowerRow77_4Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree46Norm,boundaryImPowerRow77_4Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x))))=(boundaryImPowerRow77_2Degree46Norm x).val+(boundaryFullPowerDegree46Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree46Norm x).property (boundaryFullPowerDegree46Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree46Norm,boundaryFullPowerDegree46Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x))))))=(boundaryFullPowerDegree46Block22Norm x).val+(boundaryFullPowerDegree46Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block22Norm x).property (boundaryFullPowerDegree46Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block22Norm,boundaryFullPowerDegree46Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x))=c} := by

  have he : ((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x))=(boundaryImPowerRow77_6Degree46Norm x).val+(boundaryImPowerRow77_7Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree46Norm x).property (boundaryImPowerRow77_7Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree46Norm,boundaryImPowerRow77_7Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x))))=(boundaryImPowerRow77_5Degree46Norm x).val+(boundaryFullPowerDegree46Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree46Norm x).property (boundaryFullPowerDegree46Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree46Norm,boundaryFullPowerDegree46Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))=c} := by

  have he : ((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))=(boundaryImPowerRow77_9Degree46Norm x).val+(boundaryImPowerRow77_10Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree46Norm x).property (boundaryImPowerRow77_10Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree46Norm,boundaryImPowerRow77_10Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))))=(boundaryImPowerRow77_8Degree46Norm x).val+(boundaryFullPowerDegree46Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree46Norm x).property (boundaryFullPowerDegree46Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree46Norm,boundaryFullPowerDegree46Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))))))=(boundaryFullPowerDegree46Block27Norm x).val+(boundaryFullPowerDegree46Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block27Norm x).property (boundaryFullPowerDegree46Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block27Norm,boundaryFullPowerDegree46Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x))))))))=(boundaryFullPowerDegree46Block25Norm x).val+(boundaryFullPowerDegree46Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block25Norm x).property (boundaryFullPowerDegree46Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block25Norm,boundaryFullPowerDegree46Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x))=c} := by

  have he : ((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x))=(boundaryImPowerRow77_12Degree46Norm x).val+(boundaryImPowerRow77_13Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree46Norm x).property (boundaryImPowerRow77_13Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree46Norm,boundaryImPowerRow77_13Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x))))=(boundaryImPowerRow77_11Degree46Norm x).val+(boundaryFullPowerDegree46Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree46Norm x).property (boundaryFullPowerDegree46Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree46Norm,boundaryFullPowerDegree46Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x))=c} := by

  have he : ((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x))=(boundaryImPowerRow77_15Degree46Norm x).val+(boundaryImPowerRow77_16Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree46Norm x).property (boundaryImPowerRow77_16Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree46Norm,boundaryImPowerRow77_16Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x))))=(boundaryImPowerRow77_14Degree46Norm x).val+(boundaryFullPowerDegree46Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree46Norm x).property (boundaryFullPowerDegree46Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree46Norm,boundaryFullPowerDegree46Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x))))))=(boundaryFullPowerDegree46Block33Norm x).val+(boundaryFullPowerDegree46Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block33Norm x).property (boundaryFullPowerDegree46Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block33Norm,boundaryFullPowerDegree46Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x))=c} := by

  have he : ((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x))=(boundaryImPowerRow77_18Degree46Norm x).val+(boundaryImPowerRow77_19Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree46Norm x).property (boundaryImPowerRow77_19Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree46Norm,boundaryImPowerRow77_19Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x))))=(boundaryImPowerRow77_17Degree46Norm x).val+(boundaryFullPowerDegree46Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree46Norm x).property (boundaryFullPowerDegree46Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree46Norm,boundaryFullPowerDegree46Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))=c} := by

  have he : ((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))=(boundaryImPowerRow77_21Degree46Norm x).val+(boundaryLowPowerRow77Degree46Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree46Norm x).property (boundaryLowPowerRow77Degree46Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree46Norm,boundaryLowPowerRow77Degree46Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))=(boundaryImPowerRow77_20Degree46Norm x).val+(boundaryFullPowerDegree46Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree46Norm x).property (boundaryFullPowerDegree46Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree46Norm,boundaryFullPowerDegree46Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))=(boundaryFullPowerDegree46Block38Norm x).val+(boundaryFullPowerDegree46Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block38Norm x).property (boundaryFullPowerDegree46Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block38Norm,boundaryFullPowerDegree46Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))))=(boundaryFullPowerDegree46Block36Norm x).val+(boundaryFullPowerDegree46Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block36Norm x).property (boundaryFullPowerDegree46Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block36Norm,boundaryFullPowerDegree46Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x)))))))))+(((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x)))))))))+(((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))))))=(boundaryFullPowerDegree46Block31Norm x).val+(boundaryFullPowerDegree46Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block31Norm x).property (boundaryFullPowerDegree46Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block31Norm,boundaryFullPowerDegree46Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree46Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x)))))))))+(((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x)))))))))))+(((((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x)))))))))+(((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x)))))))))+(((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x)))))))))))+(((((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x)))))))))+(((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x))))))))))))=(boundaryFullPowerDegree46Block21Norm x).val+(boundaryFullPowerDegree46Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree46Block21Norm x).property (boundaryFullPowerDegree46Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block21Norm,boundaryFullPowerDegree46Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree46Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 46 x=c} := by

  have he0 : boundaryFullPowerRow77 46 x=((((((((((boundaryRePowerRow77_0 46 x)+(boundaryRePowerRow77_1 46 x)))+(((boundaryRePowerRow77_2 46 x)+(((boundaryRePowerRow77_3 46 x)+(boundaryRePowerRow77_4 46 x)))))))+(((((boundaryRePowerRow77_5 46 x)+(((boundaryRePowerRow77_6 46 x)+(boundaryRePowerRow77_7 46 x)))))+(((boundaryRePowerRow77_8 46 x)+(((boundaryRePowerRow77_9 46 x)+(boundaryRePowerRow77_10 46 x)))))))))+(((((((boundaryRePowerRow77_11 46 x)+(((boundaryRePowerRow77_12 46 x)+(boundaryRePowerRow77_13 46 x)))))+(((boundaryRePowerRow77_14 46 x)+(((boundaryRePowerRow77_15 46 x)+(boundaryRePowerRow77_16 46 x)))))))+(((((boundaryRePowerRow77_17 46 x)+(((boundaryRePowerRow77_18 46 x)+(boundaryRePowerRow77_19 46 x)))))+(((boundaryRePowerRow77_20 46 x)+(((boundaryRePowerRow77_21 46 x)+(boundaryRePowerRow77_22 46 x)))))))))))+(((((((((boundaryImPowerRow77_0 46 x)+(boundaryImPowerRow77_1 46 x)))+(((boundaryImPowerRow77_2 46 x)+(((boundaryImPowerRow77_3 46 x)+(boundaryImPowerRow77_4 46 x)))))))+(((((boundaryImPowerRow77_5 46 x)+(((boundaryImPowerRow77_6 46 x)+(boundaryImPowerRow77_7 46 x)))))+(((boundaryImPowerRow77_8 46 x)+(((boundaryImPowerRow77_9 46 x)+(boundaryImPowerRow77_10 46 x)))))))))+(((((((boundaryImPowerRow77_11 46 x)+(((boundaryImPowerRow77_12 46 x)+(boundaryImPowerRow77_13 46 x)))))+(((boundaryImPowerRow77_14 46 x)+(((boundaryImPowerRow77_15 46 x)+(boundaryImPowerRow77_16 46 x)))))))+(((((boundaryImPowerRow77_17 46 x)+(((boundaryImPowerRow77_18 46 x)+(boundaryImPowerRow77_19 46 x)))))+(((boundaryImPowerRow77_20 46 x)+(((boundaryImPowerRow77_21 46 x)+(boundaryLowPowerRow77 46 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree46Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree46Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
