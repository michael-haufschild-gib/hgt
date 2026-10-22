import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree69Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree69Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x))=c} := by

  have he : ((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x))=(boundaryRePowerRow77_0Degree69Norm x).val+(boundaryRePowerRow77_1Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree69Norm x).property (boundaryRePowerRow77_1Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree69Norm,boundaryRePowerRow77_1Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x))=c} := by

  have he : ((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x))=(boundaryRePowerRow77_3Degree69Norm x).val+(boundaryRePowerRow77_4Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree69Norm x).property (boundaryRePowerRow77_4Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree69Norm,boundaryRePowerRow77_4Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x))))=(boundaryRePowerRow77_2Degree69Norm x).val+(boundaryFullPowerDegree69Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree69Norm x).property (boundaryFullPowerDegree69Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree69Norm,boundaryFullPowerDegree69Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x))))))=(boundaryFullPowerDegree69Block0Norm x).val+(boundaryFullPowerDegree69Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block0Norm x).property (boundaryFullPowerDegree69Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block0Norm,boundaryFullPowerDegree69Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x))=c} := by

  have he : ((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x))=(boundaryRePowerRow77_6Degree69Norm x).val+(boundaryRePowerRow77_7Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree69Norm x).property (boundaryRePowerRow77_7Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree69Norm,boundaryRePowerRow77_7Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x))))=(boundaryRePowerRow77_5Degree69Norm x).val+(boundaryFullPowerDegree69Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree69Norm x).property (boundaryFullPowerDegree69Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree69Norm,boundaryFullPowerDegree69Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))=c} := by

  have he : ((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))=(boundaryRePowerRow77_9Degree69Norm x).val+(boundaryRePowerRow77_10Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree69Norm x).property (boundaryRePowerRow77_10Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree69Norm,boundaryRePowerRow77_10Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))))=(boundaryRePowerRow77_8Degree69Norm x).val+(boundaryFullPowerDegree69Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree69Norm x).property (boundaryFullPowerDegree69Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree69Norm,boundaryFullPowerDegree69Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))))))=(boundaryFullPowerDegree69Block5Norm x).val+(boundaryFullPowerDegree69Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block5Norm x).property (boundaryFullPowerDegree69Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block5Norm,boundaryFullPowerDegree69Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x))))))))=(boundaryFullPowerDegree69Block3Norm x).val+(boundaryFullPowerDegree69Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block3Norm x).property (boundaryFullPowerDegree69Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block3Norm,boundaryFullPowerDegree69Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x))=c} := by

  have he : ((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x))=(boundaryRePowerRow77_12Degree69Norm x).val+(boundaryRePowerRow77_13Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree69Norm x).property (boundaryRePowerRow77_13Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree69Norm,boundaryRePowerRow77_13Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x))))=(boundaryRePowerRow77_11Degree69Norm x).val+(boundaryFullPowerDegree69Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree69Norm x).property (boundaryFullPowerDegree69Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree69Norm,boundaryFullPowerDegree69Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x))=c} := by

  have he : ((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x))=(boundaryRePowerRow77_15Degree69Norm x).val+(boundaryRePowerRow77_16Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree69Norm x).property (boundaryRePowerRow77_16Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree69Norm,boundaryRePowerRow77_16Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x))))=(boundaryRePowerRow77_14Degree69Norm x).val+(boundaryFullPowerDegree69Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree69Norm x).property (boundaryFullPowerDegree69Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree69Norm,boundaryFullPowerDegree69Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x))))))=(boundaryFullPowerDegree69Block11Norm x).val+(boundaryFullPowerDegree69Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block11Norm x).property (boundaryFullPowerDegree69Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block11Norm,boundaryFullPowerDegree69Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x))=c} := by

  have he : ((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x))=(boundaryRePowerRow77_18Degree69Norm x).val+(boundaryRePowerRow77_19Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree69Norm x).property (boundaryRePowerRow77_19Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree69Norm,boundaryRePowerRow77_19Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x))))=(boundaryRePowerRow77_17Degree69Norm x).val+(boundaryFullPowerDegree69Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree69Norm x).property (boundaryFullPowerDegree69Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree69Norm,boundaryFullPowerDegree69Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))=c} := by

  have he : ((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))=(boundaryRePowerRow77_21Degree69Norm x).val+(boundaryRePowerRow77_22Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree69Norm x).property (boundaryRePowerRow77_22Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree69Norm,boundaryRePowerRow77_22Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))=(boundaryRePowerRow77_20Degree69Norm x).val+(boundaryFullPowerDegree69Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree69Norm x).property (boundaryFullPowerDegree69Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree69Norm,boundaryFullPowerDegree69Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))))=(boundaryFullPowerDegree69Block16Norm x).val+(boundaryFullPowerDegree69Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block16Norm x).property (boundaryFullPowerDegree69Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block16Norm,boundaryFullPowerDegree69Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))))))=(boundaryFullPowerDegree69Block14Norm x).val+(boundaryFullPowerDegree69Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block14Norm x).property (boundaryFullPowerDegree69Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block14Norm,boundaryFullPowerDegree69Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x)))))))))+(((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x)))))))))+(((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x))))))))))=(boundaryFullPowerDegree69Block9Norm x).val+(boundaryFullPowerDegree69Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block9Norm x).property (boundaryFullPowerDegree69Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block9Norm,boundaryFullPowerDegree69Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x))=c} := by

  have he : ((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x))=(boundaryImPowerRow77_0Degree69Norm x).val+(boundaryImPowerRow77_1Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree69Norm x).property (boundaryImPowerRow77_1Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree69Norm,boundaryImPowerRow77_1Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x))=c} := by

  have he : ((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x))=(boundaryImPowerRow77_3Degree69Norm x).val+(boundaryImPowerRow77_4Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree69Norm x).property (boundaryImPowerRow77_4Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree69Norm,boundaryImPowerRow77_4Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x))))=(boundaryImPowerRow77_2Degree69Norm x).val+(boundaryFullPowerDegree69Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree69Norm x).property (boundaryFullPowerDegree69Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree69Norm,boundaryFullPowerDegree69Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x))))))=(boundaryFullPowerDegree69Block22Norm x).val+(boundaryFullPowerDegree69Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block22Norm x).property (boundaryFullPowerDegree69Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block22Norm,boundaryFullPowerDegree69Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x))=c} := by

  have he : ((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x))=(boundaryImPowerRow77_6Degree69Norm x).val+(boundaryImPowerRow77_7Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree69Norm x).property (boundaryImPowerRow77_7Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree69Norm,boundaryImPowerRow77_7Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x))))=(boundaryImPowerRow77_5Degree69Norm x).val+(boundaryFullPowerDegree69Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree69Norm x).property (boundaryFullPowerDegree69Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree69Norm,boundaryFullPowerDegree69Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))=c} := by

  have he : ((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))=(boundaryImPowerRow77_9Degree69Norm x).val+(boundaryImPowerRow77_10Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree69Norm x).property (boundaryImPowerRow77_10Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree69Norm,boundaryImPowerRow77_10Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))))=(boundaryImPowerRow77_8Degree69Norm x).val+(boundaryFullPowerDegree69Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree69Norm x).property (boundaryFullPowerDegree69Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree69Norm,boundaryFullPowerDegree69Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))))))=(boundaryFullPowerDegree69Block27Norm x).val+(boundaryFullPowerDegree69Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block27Norm x).property (boundaryFullPowerDegree69Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block27Norm,boundaryFullPowerDegree69Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x))))))))=(boundaryFullPowerDegree69Block25Norm x).val+(boundaryFullPowerDegree69Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block25Norm x).property (boundaryFullPowerDegree69Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block25Norm,boundaryFullPowerDegree69Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x))=c} := by

  have he : ((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x))=(boundaryImPowerRow77_12Degree69Norm x).val+(boundaryImPowerRow77_13Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree69Norm x).property (boundaryImPowerRow77_13Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree69Norm,boundaryImPowerRow77_13Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x))))=(boundaryImPowerRow77_11Degree69Norm x).val+(boundaryFullPowerDegree69Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree69Norm x).property (boundaryFullPowerDegree69Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree69Norm,boundaryFullPowerDegree69Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x))=c} := by

  have he : ((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x))=(boundaryImPowerRow77_15Degree69Norm x).val+(boundaryImPowerRow77_16Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree69Norm x).property (boundaryImPowerRow77_16Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree69Norm,boundaryImPowerRow77_16Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x))))=(boundaryImPowerRow77_14Degree69Norm x).val+(boundaryFullPowerDegree69Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree69Norm x).property (boundaryFullPowerDegree69Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree69Norm,boundaryFullPowerDegree69Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x))))))=(boundaryFullPowerDegree69Block33Norm x).val+(boundaryFullPowerDegree69Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block33Norm x).property (boundaryFullPowerDegree69Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block33Norm,boundaryFullPowerDegree69Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x))=c} := by

  have he : ((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x))=(boundaryImPowerRow77_18Degree69Norm x).val+(boundaryImPowerRow77_19Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree69Norm x).property (boundaryImPowerRow77_19Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree69Norm,boundaryImPowerRow77_19Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x))))=(boundaryImPowerRow77_17Degree69Norm x).val+(boundaryFullPowerDegree69Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree69Norm x).property (boundaryFullPowerDegree69Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree69Norm,boundaryFullPowerDegree69Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))=c} := by

  have he : ((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))=(boundaryImPowerRow77_21Degree69Norm x).val+(boundaryLowPowerRow77Degree69Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree69Norm x).property (boundaryLowPowerRow77Degree69Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree69Norm,boundaryLowPowerRow77Degree69Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))=(boundaryImPowerRow77_20Degree69Norm x).val+(boundaryFullPowerDegree69Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree69Norm x).property (boundaryFullPowerDegree69Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree69Norm,boundaryFullPowerDegree69Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))=(boundaryFullPowerDegree69Block38Norm x).val+(boundaryFullPowerDegree69Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block38Norm x).property (boundaryFullPowerDegree69Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block38Norm,boundaryFullPowerDegree69Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))))=(boundaryFullPowerDegree69Block36Norm x).val+(boundaryFullPowerDegree69Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block36Norm x).property (boundaryFullPowerDegree69Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block36Norm,boundaryFullPowerDegree69Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x)))))))))+(((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x)))))))))+(((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))))))=(boundaryFullPowerDegree69Block31Norm x).val+(boundaryFullPowerDegree69Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block31Norm x).property (boundaryFullPowerDegree69Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block31Norm,boundaryFullPowerDegree69Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree69Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x)))))))))+(((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x)))))))))))+(((((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x)))))))))+(((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x)))))))))+(((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x)))))))))))+(((((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x)))))))))+(((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x))))))))))))=(boundaryFullPowerDegree69Block21Norm x).val+(boundaryFullPowerDegree69Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree69Block21Norm x).property (boundaryFullPowerDegree69Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block21Norm,boundaryFullPowerDegree69Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree69Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 69 x=c} := by

  have he0 : boundaryFullPowerRow77 69 x=((((((((((boundaryRePowerRow77_0 69 x)+(boundaryRePowerRow77_1 69 x)))+(((boundaryRePowerRow77_2 69 x)+(((boundaryRePowerRow77_3 69 x)+(boundaryRePowerRow77_4 69 x)))))))+(((((boundaryRePowerRow77_5 69 x)+(((boundaryRePowerRow77_6 69 x)+(boundaryRePowerRow77_7 69 x)))))+(((boundaryRePowerRow77_8 69 x)+(((boundaryRePowerRow77_9 69 x)+(boundaryRePowerRow77_10 69 x)))))))))+(((((((boundaryRePowerRow77_11 69 x)+(((boundaryRePowerRow77_12 69 x)+(boundaryRePowerRow77_13 69 x)))))+(((boundaryRePowerRow77_14 69 x)+(((boundaryRePowerRow77_15 69 x)+(boundaryRePowerRow77_16 69 x)))))))+(((((boundaryRePowerRow77_17 69 x)+(((boundaryRePowerRow77_18 69 x)+(boundaryRePowerRow77_19 69 x)))))+(((boundaryRePowerRow77_20 69 x)+(((boundaryRePowerRow77_21 69 x)+(boundaryRePowerRow77_22 69 x)))))))))))+(((((((((boundaryImPowerRow77_0 69 x)+(boundaryImPowerRow77_1 69 x)))+(((boundaryImPowerRow77_2 69 x)+(((boundaryImPowerRow77_3 69 x)+(boundaryImPowerRow77_4 69 x)))))))+(((((boundaryImPowerRow77_5 69 x)+(((boundaryImPowerRow77_6 69 x)+(boundaryImPowerRow77_7 69 x)))))+(((boundaryImPowerRow77_8 69 x)+(((boundaryImPowerRow77_9 69 x)+(boundaryImPowerRow77_10 69 x)))))))))+(((((((boundaryImPowerRow77_11 69 x)+(((boundaryImPowerRow77_12 69 x)+(boundaryImPowerRow77_13 69 x)))))+(((boundaryImPowerRow77_14 69 x)+(((boundaryImPowerRow77_15 69 x)+(boundaryImPowerRow77_16 69 x)))))))+(((((boundaryImPowerRow77_17 69 x)+(((boundaryImPowerRow77_18 69 x)+(boundaryImPowerRow77_19 69 x)))))+(((boundaryImPowerRow77_20 69 x)+(((boundaryImPowerRow77_21 69 x)+(boundaryLowPowerRow77 69 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree69Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree69Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
