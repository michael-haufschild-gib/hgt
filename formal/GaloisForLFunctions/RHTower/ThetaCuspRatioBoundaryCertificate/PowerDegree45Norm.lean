import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree45Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree45Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x))=c} := by

  have he : ((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x))=(boundaryRePowerRow77_0Degree45Norm x).val+(boundaryRePowerRow77_1Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree45Norm x).property (boundaryRePowerRow77_1Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree45Norm,boundaryRePowerRow77_1Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x))=c} := by

  have he : ((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x))=(boundaryRePowerRow77_3Degree45Norm x).val+(boundaryRePowerRow77_4Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree45Norm x).property (boundaryRePowerRow77_4Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree45Norm,boundaryRePowerRow77_4Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x))))=(boundaryRePowerRow77_2Degree45Norm x).val+(boundaryFullPowerDegree45Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree45Norm x).property (boundaryFullPowerDegree45Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree45Norm,boundaryFullPowerDegree45Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x))))))=(boundaryFullPowerDegree45Block0Norm x).val+(boundaryFullPowerDegree45Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block0Norm x).property (boundaryFullPowerDegree45Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block0Norm,boundaryFullPowerDegree45Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x))=c} := by

  have he : ((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x))=(boundaryRePowerRow77_6Degree45Norm x).val+(boundaryRePowerRow77_7Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree45Norm x).property (boundaryRePowerRow77_7Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree45Norm,boundaryRePowerRow77_7Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x))))=(boundaryRePowerRow77_5Degree45Norm x).val+(boundaryFullPowerDegree45Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree45Norm x).property (boundaryFullPowerDegree45Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree45Norm,boundaryFullPowerDegree45Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))=c} := by

  have he : ((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))=(boundaryRePowerRow77_9Degree45Norm x).val+(boundaryRePowerRow77_10Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree45Norm x).property (boundaryRePowerRow77_10Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree45Norm,boundaryRePowerRow77_10Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))))=(boundaryRePowerRow77_8Degree45Norm x).val+(boundaryFullPowerDegree45Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree45Norm x).property (boundaryFullPowerDegree45Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree45Norm,boundaryFullPowerDegree45Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))))))=(boundaryFullPowerDegree45Block5Norm x).val+(boundaryFullPowerDegree45Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block5Norm x).property (boundaryFullPowerDegree45Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block5Norm,boundaryFullPowerDegree45Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x))))))))=(boundaryFullPowerDegree45Block3Norm x).val+(boundaryFullPowerDegree45Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block3Norm x).property (boundaryFullPowerDegree45Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block3Norm,boundaryFullPowerDegree45Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x))=c} := by

  have he : ((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x))=(boundaryRePowerRow77_12Degree45Norm x).val+(boundaryRePowerRow77_13Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree45Norm x).property (boundaryRePowerRow77_13Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree45Norm,boundaryRePowerRow77_13Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x))))=(boundaryRePowerRow77_11Degree45Norm x).val+(boundaryFullPowerDegree45Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree45Norm x).property (boundaryFullPowerDegree45Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree45Norm,boundaryFullPowerDegree45Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x))=c} := by

  have he : ((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x))=(boundaryRePowerRow77_15Degree45Norm x).val+(boundaryRePowerRow77_16Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree45Norm x).property (boundaryRePowerRow77_16Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree45Norm,boundaryRePowerRow77_16Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x))))=(boundaryRePowerRow77_14Degree45Norm x).val+(boundaryFullPowerDegree45Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree45Norm x).property (boundaryFullPowerDegree45Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree45Norm,boundaryFullPowerDegree45Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x))))))=(boundaryFullPowerDegree45Block11Norm x).val+(boundaryFullPowerDegree45Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block11Norm x).property (boundaryFullPowerDegree45Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block11Norm,boundaryFullPowerDegree45Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x))=c} := by

  have he : ((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x))=(boundaryRePowerRow77_18Degree45Norm x).val+(boundaryRePowerRow77_19Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree45Norm x).property (boundaryRePowerRow77_19Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree45Norm,boundaryRePowerRow77_19Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x))))=(boundaryRePowerRow77_17Degree45Norm x).val+(boundaryFullPowerDegree45Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree45Norm x).property (boundaryFullPowerDegree45Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree45Norm,boundaryFullPowerDegree45Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))=c} := by

  have he : ((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))=(boundaryRePowerRow77_21Degree45Norm x).val+(boundaryRePowerRow77_22Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree45Norm x).property (boundaryRePowerRow77_22Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree45Norm,boundaryRePowerRow77_22Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))=(boundaryRePowerRow77_20Degree45Norm x).val+(boundaryFullPowerDegree45Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree45Norm x).property (boundaryFullPowerDegree45Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree45Norm,boundaryFullPowerDegree45Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))))=(boundaryFullPowerDegree45Block16Norm x).val+(boundaryFullPowerDegree45Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block16Norm x).property (boundaryFullPowerDegree45Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block16Norm,boundaryFullPowerDegree45Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))))))=(boundaryFullPowerDegree45Block14Norm x).val+(boundaryFullPowerDegree45Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block14Norm x).property (boundaryFullPowerDegree45Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block14Norm,boundaryFullPowerDegree45Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x)))))))))+(((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x)))))))))+(((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x))))))))))=(boundaryFullPowerDegree45Block9Norm x).val+(boundaryFullPowerDegree45Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block9Norm x).property (boundaryFullPowerDegree45Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block9Norm,boundaryFullPowerDegree45Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x))=c} := by

  have he : ((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x))=(boundaryImPowerRow77_0Degree45Norm x).val+(boundaryImPowerRow77_1Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree45Norm x).property (boundaryImPowerRow77_1Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree45Norm,boundaryImPowerRow77_1Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x))=c} := by

  have he : ((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x))=(boundaryImPowerRow77_3Degree45Norm x).val+(boundaryImPowerRow77_4Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree45Norm x).property (boundaryImPowerRow77_4Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree45Norm,boundaryImPowerRow77_4Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x))))=(boundaryImPowerRow77_2Degree45Norm x).val+(boundaryFullPowerDegree45Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree45Norm x).property (boundaryFullPowerDegree45Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree45Norm,boundaryFullPowerDegree45Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x))))))=(boundaryFullPowerDegree45Block22Norm x).val+(boundaryFullPowerDegree45Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block22Norm x).property (boundaryFullPowerDegree45Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block22Norm,boundaryFullPowerDegree45Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x))=c} := by

  have he : ((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x))=(boundaryImPowerRow77_6Degree45Norm x).val+(boundaryImPowerRow77_7Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree45Norm x).property (boundaryImPowerRow77_7Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree45Norm,boundaryImPowerRow77_7Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x))))=(boundaryImPowerRow77_5Degree45Norm x).val+(boundaryFullPowerDegree45Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree45Norm x).property (boundaryFullPowerDegree45Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree45Norm,boundaryFullPowerDegree45Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))=c} := by

  have he : ((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))=(boundaryImPowerRow77_9Degree45Norm x).val+(boundaryImPowerRow77_10Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree45Norm x).property (boundaryImPowerRow77_10Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree45Norm,boundaryImPowerRow77_10Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))))=(boundaryImPowerRow77_8Degree45Norm x).val+(boundaryFullPowerDegree45Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree45Norm x).property (boundaryFullPowerDegree45Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree45Norm,boundaryFullPowerDegree45Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))))))=(boundaryFullPowerDegree45Block27Norm x).val+(boundaryFullPowerDegree45Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block27Norm x).property (boundaryFullPowerDegree45Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block27Norm,boundaryFullPowerDegree45Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x))))))))=(boundaryFullPowerDegree45Block25Norm x).val+(boundaryFullPowerDegree45Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block25Norm x).property (boundaryFullPowerDegree45Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block25Norm,boundaryFullPowerDegree45Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x))=c} := by

  have he : ((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x))=(boundaryImPowerRow77_12Degree45Norm x).val+(boundaryImPowerRow77_13Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree45Norm x).property (boundaryImPowerRow77_13Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree45Norm,boundaryImPowerRow77_13Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x))))=(boundaryImPowerRow77_11Degree45Norm x).val+(boundaryFullPowerDegree45Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree45Norm x).property (boundaryFullPowerDegree45Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree45Norm,boundaryFullPowerDegree45Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x))=c} := by

  have he : ((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x))=(boundaryImPowerRow77_15Degree45Norm x).val+(boundaryImPowerRow77_16Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree45Norm x).property (boundaryImPowerRow77_16Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree45Norm,boundaryImPowerRow77_16Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x))))=(boundaryImPowerRow77_14Degree45Norm x).val+(boundaryFullPowerDegree45Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree45Norm x).property (boundaryFullPowerDegree45Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree45Norm,boundaryFullPowerDegree45Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x))))))=(boundaryFullPowerDegree45Block33Norm x).val+(boundaryFullPowerDegree45Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block33Norm x).property (boundaryFullPowerDegree45Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block33Norm,boundaryFullPowerDegree45Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x))=c} := by

  have he : ((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x))=(boundaryImPowerRow77_18Degree45Norm x).val+(boundaryImPowerRow77_19Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree45Norm x).property (boundaryImPowerRow77_19Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree45Norm,boundaryImPowerRow77_19Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x))))=(boundaryImPowerRow77_17Degree45Norm x).val+(boundaryFullPowerDegree45Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree45Norm x).property (boundaryFullPowerDegree45Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree45Norm,boundaryFullPowerDegree45Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))=c} := by

  have he : ((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))=(boundaryImPowerRow77_21Degree45Norm x).val+(boundaryLowPowerRow77Degree45Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree45Norm x).property (boundaryLowPowerRow77Degree45Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree45Norm,boundaryLowPowerRow77Degree45Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))=(boundaryImPowerRow77_20Degree45Norm x).val+(boundaryFullPowerDegree45Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree45Norm x).property (boundaryFullPowerDegree45Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree45Norm,boundaryFullPowerDegree45Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))=(boundaryFullPowerDegree45Block38Norm x).val+(boundaryFullPowerDegree45Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block38Norm x).property (boundaryFullPowerDegree45Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block38Norm,boundaryFullPowerDegree45Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))))=(boundaryFullPowerDegree45Block36Norm x).val+(boundaryFullPowerDegree45Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block36Norm x).property (boundaryFullPowerDegree45Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block36Norm,boundaryFullPowerDegree45Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x)))))))))+(((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x)))))))))+(((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))))))=(boundaryFullPowerDegree45Block31Norm x).val+(boundaryFullPowerDegree45Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block31Norm x).property (boundaryFullPowerDegree45Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block31Norm,boundaryFullPowerDegree45Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree45Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x)))))))))+(((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x)))))))))))+(((((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x)))))))))+(((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x)))))))))+(((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x)))))))))))+(((((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x)))))))))+(((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x))))))))))))=(boundaryFullPowerDegree45Block21Norm x).val+(boundaryFullPowerDegree45Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree45Block21Norm x).property (boundaryFullPowerDegree45Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block21Norm,boundaryFullPowerDegree45Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree45Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 45 x=c} := by

  have he0 : boundaryFullPowerRow77 45 x=((((((((((boundaryRePowerRow77_0 45 x)+(boundaryRePowerRow77_1 45 x)))+(((boundaryRePowerRow77_2 45 x)+(((boundaryRePowerRow77_3 45 x)+(boundaryRePowerRow77_4 45 x)))))))+(((((boundaryRePowerRow77_5 45 x)+(((boundaryRePowerRow77_6 45 x)+(boundaryRePowerRow77_7 45 x)))))+(((boundaryRePowerRow77_8 45 x)+(((boundaryRePowerRow77_9 45 x)+(boundaryRePowerRow77_10 45 x)))))))))+(((((((boundaryRePowerRow77_11 45 x)+(((boundaryRePowerRow77_12 45 x)+(boundaryRePowerRow77_13 45 x)))))+(((boundaryRePowerRow77_14 45 x)+(((boundaryRePowerRow77_15 45 x)+(boundaryRePowerRow77_16 45 x)))))))+(((((boundaryRePowerRow77_17 45 x)+(((boundaryRePowerRow77_18 45 x)+(boundaryRePowerRow77_19 45 x)))))+(((boundaryRePowerRow77_20 45 x)+(((boundaryRePowerRow77_21 45 x)+(boundaryRePowerRow77_22 45 x)))))))))))+(((((((((boundaryImPowerRow77_0 45 x)+(boundaryImPowerRow77_1 45 x)))+(((boundaryImPowerRow77_2 45 x)+(((boundaryImPowerRow77_3 45 x)+(boundaryImPowerRow77_4 45 x)))))))+(((((boundaryImPowerRow77_5 45 x)+(((boundaryImPowerRow77_6 45 x)+(boundaryImPowerRow77_7 45 x)))))+(((boundaryImPowerRow77_8 45 x)+(((boundaryImPowerRow77_9 45 x)+(boundaryImPowerRow77_10 45 x)))))))))+(((((((boundaryImPowerRow77_11 45 x)+(((boundaryImPowerRow77_12 45 x)+(boundaryImPowerRow77_13 45 x)))))+(((boundaryImPowerRow77_14 45 x)+(((boundaryImPowerRow77_15 45 x)+(boundaryImPowerRow77_16 45 x)))))))+(((((boundaryImPowerRow77_17 45 x)+(((boundaryImPowerRow77_18 45 x)+(boundaryImPowerRow77_19 45 x)))))+(((boundaryImPowerRow77_20 45 x)+(((boundaryImPowerRow77_21 45 x)+(boundaryLowPowerRow77 45 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree45Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree45Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
