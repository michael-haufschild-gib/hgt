import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree61Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree61Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x))=c} := by

  have he : ((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x))=(boundaryRePowerRow77_0Degree61Norm x).val+(boundaryRePowerRow77_1Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree61Norm x).property (boundaryRePowerRow77_1Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree61Norm,boundaryRePowerRow77_1Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x))=c} := by

  have he : ((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x))=(boundaryRePowerRow77_3Degree61Norm x).val+(boundaryRePowerRow77_4Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree61Norm x).property (boundaryRePowerRow77_4Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree61Norm,boundaryRePowerRow77_4Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x))))=(boundaryRePowerRow77_2Degree61Norm x).val+(boundaryFullPowerDegree61Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree61Norm x).property (boundaryFullPowerDegree61Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree61Norm,boundaryFullPowerDegree61Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x))))))=(boundaryFullPowerDegree61Block0Norm x).val+(boundaryFullPowerDegree61Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block0Norm x).property (boundaryFullPowerDegree61Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block0Norm,boundaryFullPowerDegree61Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x))=c} := by

  have he : ((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x))=(boundaryRePowerRow77_6Degree61Norm x).val+(boundaryRePowerRow77_7Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree61Norm x).property (boundaryRePowerRow77_7Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree61Norm,boundaryRePowerRow77_7Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x))))=(boundaryRePowerRow77_5Degree61Norm x).val+(boundaryFullPowerDegree61Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree61Norm x).property (boundaryFullPowerDegree61Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree61Norm,boundaryFullPowerDegree61Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))=c} := by

  have he : ((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))=(boundaryRePowerRow77_9Degree61Norm x).val+(boundaryRePowerRow77_10Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree61Norm x).property (boundaryRePowerRow77_10Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree61Norm,boundaryRePowerRow77_10Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))))=(boundaryRePowerRow77_8Degree61Norm x).val+(boundaryFullPowerDegree61Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree61Norm x).property (boundaryFullPowerDegree61Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree61Norm,boundaryFullPowerDegree61Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))))))=(boundaryFullPowerDegree61Block5Norm x).val+(boundaryFullPowerDegree61Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block5Norm x).property (boundaryFullPowerDegree61Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block5Norm,boundaryFullPowerDegree61Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x))))))))=(boundaryFullPowerDegree61Block3Norm x).val+(boundaryFullPowerDegree61Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block3Norm x).property (boundaryFullPowerDegree61Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block3Norm,boundaryFullPowerDegree61Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x))=c} := by

  have he : ((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x))=(boundaryRePowerRow77_12Degree61Norm x).val+(boundaryRePowerRow77_13Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree61Norm x).property (boundaryRePowerRow77_13Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree61Norm,boundaryRePowerRow77_13Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x))))=(boundaryRePowerRow77_11Degree61Norm x).val+(boundaryFullPowerDegree61Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree61Norm x).property (boundaryFullPowerDegree61Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree61Norm,boundaryFullPowerDegree61Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x))=c} := by

  have he : ((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x))=(boundaryRePowerRow77_15Degree61Norm x).val+(boundaryRePowerRow77_16Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree61Norm x).property (boundaryRePowerRow77_16Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree61Norm,boundaryRePowerRow77_16Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x))))=(boundaryRePowerRow77_14Degree61Norm x).val+(boundaryFullPowerDegree61Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree61Norm x).property (boundaryFullPowerDegree61Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree61Norm,boundaryFullPowerDegree61Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x))))))=(boundaryFullPowerDegree61Block11Norm x).val+(boundaryFullPowerDegree61Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block11Norm x).property (boundaryFullPowerDegree61Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block11Norm,boundaryFullPowerDegree61Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x))=c} := by

  have he : ((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x))=(boundaryRePowerRow77_18Degree61Norm x).val+(boundaryRePowerRow77_19Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree61Norm x).property (boundaryRePowerRow77_19Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree61Norm,boundaryRePowerRow77_19Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x))))=(boundaryRePowerRow77_17Degree61Norm x).val+(boundaryFullPowerDegree61Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree61Norm x).property (boundaryFullPowerDegree61Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree61Norm,boundaryFullPowerDegree61Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))=c} := by

  have he : ((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))=(boundaryRePowerRow77_21Degree61Norm x).val+(boundaryRePowerRow77_22Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree61Norm x).property (boundaryRePowerRow77_22Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree61Norm,boundaryRePowerRow77_22Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))=(boundaryRePowerRow77_20Degree61Norm x).val+(boundaryFullPowerDegree61Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree61Norm x).property (boundaryFullPowerDegree61Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree61Norm,boundaryFullPowerDegree61Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))))=(boundaryFullPowerDegree61Block16Norm x).val+(boundaryFullPowerDegree61Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block16Norm x).property (boundaryFullPowerDegree61Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block16Norm,boundaryFullPowerDegree61Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))))))=(boundaryFullPowerDegree61Block14Norm x).val+(boundaryFullPowerDegree61Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block14Norm x).property (boundaryFullPowerDegree61Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block14Norm,boundaryFullPowerDegree61Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x)))))))))+(((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x)))))))))+(((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x))))))))))=(boundaryFullPowerDegree61Block9Norm x).val+(boundaryFullPowerDegree61Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block9Norm x).property (boundaryFullPowerDegree61Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block9Norm,boundaryFullPowerDegree61Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x))=c} := by

  have he : ((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x))=(boundaryImPowerRow77_0Degree61Norm x).val+(boundaryImPowerRow77_1Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree61Norm x).property (boundaryImPowerRow77_1Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree61Norm,boundaryImPowerRow77_1Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x))=c} := by

  have he : ((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x))=(boundaryImPowerRow77_3Degree61Norm x).val+(boundaryImPowerRow77_4Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree61Norm x).property (boundaryImPowerRow77_4Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree61Norm,boundaryImPowerRow77_4Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x))))=(boundaryImPowerRow77_2Degree61Norm x).val+(boundaryFullPowerDegree61Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree61Norm x).property (boundaryFullPowerDegree61Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree61Norm,boundaryFullPowerDegree61Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x))))))=(boundaryFullPowerDegree61Block22Norm x).val+(boundaryFullPowerDegree61Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block22Norm x).property (boundaryFullPowerDegree61Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block22Norm,boundaryFullPowerDegree61Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x))=c} := by

  have he : ((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x))=(boundaryImPowerRow77_6Degree61Norm x).val+(boundaryImPowerRow77_7Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree61Norm x).property (boundaryImPowerRow77_7Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree61Norm,boundaryImPowerRow77_7Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x))))=(boundaryImPowerRow77_5Degree61Norm x).val+(boundaryFullPowerDegree61Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree61Norm x).property (boundaryFullPowerDegree61Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree61Norm,boundaryFullPowerDegree61Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))=c} := by

  have he : ((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))=(boundaryImPowerRow77_9Degree61Norm x).val+(boundaryImPowerRow77_10Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree61Norm x).property (boundaryImPowerRow77_10Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree61Norm,boundaryImPowerRow77_10Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))))=(boundaryImPowerRow77_8Degree61Norm x).val+(boundaryFullPowerDegree61Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree61Norm x).property (boundaryFullPowerDegree61Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree61Norm,boundaryFullPowerDegree61Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))))))=(boundaryFullPowerDegree61Block27Norm x).val+(boundaryFullPowerDegree61Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block27Norm x).property (boundaryFullPowerDegree61Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block27Norm,boundaryFullPowerDegree61Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x))))))))=(boundaryFullPowerDegree61Block25Norm x).val+(boundaryFullPowerDegree61Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block25Norm x).property (boundaryFullPowerDegree61Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block25Norm,boundaryFullPowerDegree61Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x))=c} := by

  have he : ((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x))=(boundaryImPowerRow77_12Degree61Norm x).val+(boundaryImPowerRow77_13Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree61Norm x).property (boundaryImPowerRow77_13Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree61Norm,boundaryImPowerRow77_13Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x))))=(boundaryImPowerRow77_11Degree61Norm x).val+(boundaryFullPowerDegree61Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree61Norm x).property (boundaryFullPowerDegree61Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree61Norm,boundaryFullPowerDegree61Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x))=c} := by

  have he : ((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x))=(boundaryImPowerRow77_15Degree61Norm x).val+(boundaryImPowerRow77_16Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree61Norm x).property (boundaryImPowerRow77_16Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree61Norm,boundaryImPowerRow77_16Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x))))=(boundaryImPowerRow77_14Degree61Norm x).val+(boundaryFullPowerDegree61Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree61Norm x).property (boundaryFullPowerDegree61Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree61Norm,boundaryFullPowerDegree61Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x))))))=(boundaryFullPowerDegree61Block33Norm x).val+(boundaryFullPowerDegree61Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block33Norm x).property (boundaryFullPowerDegree61Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block33Norm,boundaryFullPowerDegree61Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x))=c} := by

  have he : ((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x))=(boundaryImPowerRow77_18Degree61Norm x).val+(boundaryImPowerRow77_19Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree61Norm x).property (boundaryImPowerRow77_19Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree61Norm,boundaryImPowerRow77_19Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x))))=(boundaryImPowerRow77_17Degree61Norm x).val+(boundaryFullPowerDegree61Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree61Norm x).property (boundaryFullPowerDegree61Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree61Norm,boundaryFullPowerDegree61Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))=c} := by

  have he : ((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))=(boundaryImPowerRow77_21Degree61Norm x).val+(boundaryLowPowerRow77Degree61Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree61Norm x).property (boundaryLowPowerRow77Degree61Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree61Norm,boundaryLowPowerRow77Degree61Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))=(boundaryImPowerRow77_20Degree61Norm x).val+(boundaryFullPowerDegree61Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree61Norm x).property (boundaryFullPowerDegree61Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree61Norm,boundaryFullPowerDegree61Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))=(boundaryFullPowerDegree61Block38Norm x).val+(boundaryFullPowerDegree61Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block38Norm x).property (boundaryFullPowerDegree61Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block38Norm,boundaryFullPowerDegree61Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))))=(boundaryFullPowerDegree61Block36Norm x).val+(boundaryFullPowerDegree61Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block36Norm x).property (boundaryFullPowerDegree61Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block36Norm,boundaryFullPowerDegree61Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x)))))))))+(((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x)))))))))+(((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))))))=(boundaryFullPowerDegree61Block31Norm x).val+(boundaryFullPowerDegree61Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block31Norm x).property (boundaryFullPowerDegree61Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block31Norm,boundaryFullPowerDegree61Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree61Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x)))))))))+(((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x)))))))))))+(((((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x)))))))))+(((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x)))))))))+(((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x)))))))))))+(((((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x)))))))))+(((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x))))))))))))=(boundaryFullPowerDegree61Block21Norm x).val+(boundaryFullPowerDegree61Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree61Block21Norm x).property (boundaryFullPowerDegree61Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block21Norm,boundaryFullPowerDegree61Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree61Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 61 x=c} := by

  have he0 : boundaryFullPowerRow77 61 x=((((((((((boundaryRePowerRow77_0 61 x)+(boundaryRePowerRow77_1 61 x)))+(((boundaryRePowerRow77_2 61 x)+(((boundaryRePowerRow77_3 61 x)+(boundaryRePowerRow77_4 61 x)))))))+(((((boundaryRePowerRow77_5 61 x)+(((boundaryRePowerRow77_6 61 x)+(boundaryRePowerRow77_7 61 x)))))+(((boundaryRePowerRow77_8 61 x)+(((boundaryRePowerRow77_9 61 x)+(boundaryRePowerRow77_10 61 x)))))))))+(((((((boundaryRePowerRow77_11 61 x)+(((boundaryRePowerRow77_12 61 x)+(boundaryRePowerRow77_13 61 x)))))+(((boundaryRePowerRow77_14 61 x)+(((boundaryRePowerRow77_15 61 x)+(boundaryRePowerRow77_16 61 x)))))))+(((((boundaryRePowerRow77_17 61 x)+(((boundaryRePowerRow77_18 61 x)+(boundaryRePowerRow77_19 61 x)))))+(((boundaryRePowerRow77_20 61 x)+(((boundaryRePowerRow77_21 61 x)+(boundaryRePowerRow77_22 61 x)))))))))))+(((((((((boundaryImPowerRow77_0 61 x)+(boundaryImPowerRow77_1 61 x)))+(((boundaryImPowerRow77_2 61 x)+(((boundaryImPowerRow77_3 61 x)+(boundaryImPowerRow77_4 61 x)))))))+(((((boundaryImPowerRow77_5 61 x)+(((boundaryImPowerRow77_6 61 x)+(boundaryImPowerRow77_7 61 x)))))+(((boundaryImPowerRow77_8 61 x)+(((boundaryImPowerRow77_9 61 x)+(boundaryImPowerRow77_10 61 x)))))))))+(((((((boundaryImPowerRow77_11 61 x)+(((boundaryImPowerRow77_12 61 x)+(boundaryImPowerRow77_13 61 x)))))+(((boundaryImPowerRow77_14 61 x)+(((boundaryImPowerRow77_15 61 x)+(boundaryImPowerRow77_16 61 x)))))))+(((((boundaryImPowerRow77_17 61 x)+(((boundaryImPowerRow77_18 61 x)+(boundaryImPowerRow77_19 61 x)))))+(((boundaryImPowerRow77_20 61 x)+(((boundaryImPowerRow77_21 61 x)+(boundaryLowPowerRow77 61 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree61Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree61Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
