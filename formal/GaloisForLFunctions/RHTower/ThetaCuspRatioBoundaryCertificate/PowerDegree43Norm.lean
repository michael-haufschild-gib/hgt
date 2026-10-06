import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree43Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree43Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x))=c} := by

  have he : ((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x))=(boundaryRePowerRow77_0Degree43Norm x).val+(boundaryRePowerRow77_1Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree43Norm x).property (boundaryRePowerRow77_1Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree43Norm,boundaryRePowerRow77_1Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x))=c} := by

  have he : ((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x))=(boundaryRePowerRow77_3Degree43Norm x).val+(boundaryRePowerRow77_4Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree43Norm x).property (boundaryRePowerRow77_4Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree43Norm,boundaryRePowerRow77_4Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x))))=(boundaryRePowerRow77_2Degree43Norm x).val+(boundaryFullPowerDegree43Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree43Norm x).property (boundaryFullPowerDegree43Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree43Norm,boundaryFullPowerDegree43Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x))))))=(boundaryFullPowerDegree43Block0Norm x).val+(boundaryFullPowerDegree43Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block0Norm x).property (boundaryFullPowerDegree43Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block0Norm,boundaryFullPowerDegree43Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x))=c} := by

  have he : ((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x))=(boundaryRePowerRow77_6Degree43Norm x).val+(boundaryRePowerRow77_7Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree43Norm x).property (boundaryRePowerRow77_7Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree43Norm,boundaryRePowerRow77_7Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x))))=(boundaryRePowerRow77_5Degree43Norm x).val+(boundaryFullPowerDegree43Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree43Norm x).property (boundaryFullPowerDegree43Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree43Norm,boundaryFullPowerDegree43Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))=c} := by

  have he : ((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))=(boundaryRePowerRow77_9Degree43Norm x).val+(boundaryRePowerRow77_10Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree43Norm x).property (boundaryRePowerRow77_10Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree43Norm,boundaryRePowerRow77_10Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))))=(boundaryRePowerRow77_8Degree43Norm x).val+(boundaryFullPowerDegree43Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree43Norm x).property (boundaryFullPowerDegree43Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree43Norm,boundaryFullPowerDegree43Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))))))=(boundaryFullPowerDegree43Block5Norm x).val+(boundaryFullPowerDegree43Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block5Norm x).property (boundaryFullPowerDegree43Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block5Norm,boundaryFullPowerDegree43Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x))))))))=(boundaryFullPowerDegree43Block3Norm x).val+(boundaryFullPowerDegree43Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block3Norm x).property (boundaryFullPowerDegree43Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block3Norm,boundaryFullPowerDegree43Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x))=c} := by

  have he : ((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x))=(boundaryRePowerRow77_12Degree43Norm x).val+(boundaryRePowerRow77_13Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree43Norm x).property (boundaryRePowerRow77_13Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree43Norm,boundaryRePowerRow77_13Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x))))=(boundaryRePowerRow77_11Degree43Norm x).val+(boundaryFullPowerDegree43Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree43Norm x).property (boundaryFullPowerDegree43Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree43Norm,boundaryFullPowerDegree43Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x))=c} := by

  have he : ((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x))=(boundaryRePowerRow77_15Degree43Norm x).val+(boundaryRePowerRow77_16Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree43Norm x).property (boundaryRePowerRow77_16Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree43Norm,boundaryRePowerRow77_16Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x))))=(boundaryRePowerRow77_14Degree43Norm x).val+(boundaryFullPowerDegree43Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree43Norm x).property (boundaryFullPowerDegree43Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree43Norm,boundaryFullPowerDegree43Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x))))))=(boundaryFullPowerDegree43Block11Norm x).val+(boundaryFullPowerDegree43Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block11Norm x).property (boundaryFullPowerDegree43Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block11Norm,boundaryFullPowerDegree43Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x))=c} := by

  have he : ((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x))=(boundaryRePowerRow77_18Degree43Norm x).val+(boundaryRePowerRow77_19Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree43Norm x).property (boundaryRePowerRow77_19Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree43Norm,boundaryRePowerRow77_19Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x))))=(boundaryRePowerRow77_17Degree43Norm x).val+(boundaryFullPowerDegree43Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree43Norm x).property (boundaryFullPowerDegree43Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree43Norm,boundaryFullPowerDegree43Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))=c} := by

  have he : ((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))=(boundaryRePowerRow77_21Degree43Norm x).val+(boundaryRePowerRow77_22Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree43Norm x).property (boundaryRePowerRow77_22Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree43Norm,boundaryRePowerRow77_22Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))=(boundaryRePowerRow77_20Degree43Norm x).val+(boundaryFullPowerDegree43Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree43Norm x).property (boundaryFullPowerDegree43Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree43Norm,boundaryFullPowerDegree43Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))))=(boundaryFullPowerDegree43Block16Norm x).val+(boundaryFullPowerDegree43Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block16Norm x).property (boundaryFullPowerDegree43Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block16Norm,boundaryFullPowerDegree43Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))))))=(boundaryFullPowerDegree43Block14Norm x).val+(boundaryFullPowerDegree43Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block14Norm x).property (boundaryFullPowerDegree43Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block14Norm,boundaryFullPowerDegree43Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x)))))))))+(((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x)))))))))+(((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x))))))))))=(boundaryFullPowerDegree43Block9Norm x).val+(boundaryFullPowerDegree43Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block9Norm x).property (boundaryFullPowerDegree43Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block9Norm,boundaryFullPowerDegree43Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x))=c} := by

  have he : ((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x))=(boundaryImPowerRow77_0Degree43Norm x).val+(boundaryImPowerRow77_1Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree43Norm x).property (boundaryImPowerRow77_1Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree43Norm,boundaryImPowerRow77_1Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x))=c} := by

  have he : ((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x))=(boundaryImPowerRow77_3Degree43Norm x).val+(boundaryImPowerRow77_4Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree43Norm x).property (boundaryImPowerRow77_4Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree43Norm,boundaryImPowerRow77_4Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x))))=(boundaryImPowerRow77_2Degree43Norm x).val+(boundaryFullPowerDegree43Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree43Norm x).property (boundaryFullPowerDegree43Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree43Norm,boundaryFullPowerDegree43Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x))))))=(boundaryFullPowerDegree43Block22Norm x).val+(boundaryFullPowerDegree43Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block22Norm x).property (boundaryFullPowerDegree43Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block22Norm,boundaryFullPowerDegree43Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x))=c} := by

  have he : ((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x))=(boundaryImPowerRow77_6Degree43Norm x).val+(boundaryImPowerRow77_7Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree43Norm x).property (boundaryImPowerRow77_7Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree43Norm,boundaryImPowerRow77_7Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x))))=(boundaryImPowerRow77_5Degree43Norm x).val+(boundaryFullPowerDegree43Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree43Norm x).property (boundaryFullPowerDegree43Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree43Norm,boundaryFullPowerDegree43Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))=c} := by

  have he : ((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))=(boundaryImPowerRow77_9Degree43Norm x).val+(boundaryImPowerRow77_10Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree43Norm x).property (boundaryImPowerRow77_10Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree43Norm,boundaryImPowerRow77_10Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))))=(boundaryImPowerRow77_8Degree43Norm x).val+(boundaryFullPowerDegree43Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree43Norm x).property (boundaryFullPowerDegree43Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree43Norm,boundaryFullPowerDegree43Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))))))=(boundaryFullPowerDegree43Block27Norm x).val+(boundaryFullPowerDegree43Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block27Norm x).property (boundaryFullPowerDegree43Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block27Norm,boundaryFullPowerDegree43Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x))))))))=(boundaryFullPowerDegree43Block25Norm x).val+(boundaryFullPowerDegree43Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block25Norm x).property (boundaryFullPowerDegree43Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block25Norm,boundaryFullPowerDegree43Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x))=c} := by

  have he : ((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x))=(boundaryImPowerRow77_12Degree43Norm x).val+(boundaryImPowerRow77_13Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree43Norm x).property (boundaryImPowerRow77_13Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree43Norm,boundaryImPowerRow77_13Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x))))=(boundaryImPowerRow77_11Degree43Norm x).val+(boundaryFullPowerDegree43Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree43Norm x).property (boundaryFullPowerDegree43Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree43Norm,boundaryFullPowerDegree43Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x))=c} := by

  have he : ((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x))=(boundaryImPowerRow77_15Degree43Norm x).val+(boundaryImPowerRow77_16Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree43Norm x).property (boundaryImPowerRow77_16Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree43Norm,boundaryImPowerRow77_16Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x))))=(boundaryImPowerRow77_14Degree43Norm x).val+(boundaryFullPowerDegree43Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree43Norm x).property (boundaryFullPowerDegree43Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree43Norm,boundaryFullPowerDegree43Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x))))))=(boundaryFullPowerDegree43Block33Norm x).val+(boundaryFullPowerDegree43Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block33Norm x).property (boundaryFullPowerDegree43Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block33Norm,boundaryFullPowerDegree43Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x))=c} := by

  have he : ((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x))=(boundaryImPowerRow77_18Degree43Norm x).val+(boundaryImPowerRow77_19Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree43Norm x).property (boundaryImPowerRow77_19Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree43Norm,boundaryImPowerRow77_19Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x))))=(boundaryImPowerRow77_17Degree43Norm x).val+(boundaryFullPowerDegree43Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree43Norm x).property (boundaryFullPowerDegree43Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree43Norm,boundaryFullPowerDegree43Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))=c} := by

  have he : ((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))=(boundaryImPowerRow77_21Degree43Norm x).val+(boundaryLowPowerRow77Degree43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree43Norm x).property (boundaryLowPowerRow77Degree43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree43Norm,boundaryLowPowerRow77Degree43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))=(boundaryImPowerRow77_20Degree43Norm x).val+(boundaryFullPowerDegree43Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree43Norm x).property (boundaryFullPowerDegree43Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree43Norm,boundaryFullPowerDegree43Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))=(boundaryFullPowerDegree43Block38Norm x).val+(boundaryFullPowerDegree43Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block38Norm x).property (boundaryFullPowerDegree43Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block38Norm,boundaryFullPowerDegree43Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))))=(boundaryFullPowerDegree43Block36Norm x).val+(boundaryFullPowerDegree43Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block36Norm x).property (boundaryFullPowerDegree43Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block36Norm,boundaryFullPowerDegree43Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x)))))))))+(((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x)))))))))+(((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))))))=(boundaryFullPowerDegree43Block31Norm x).val+(boundaryFullPowerDegree43Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block31Norm x).property (boundaryFullPowerDegree43Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block31Norm,boundaryFullPowerDegree43Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree43Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x)))))))))+(((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x)))))))))))+(((((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x)))))))))+(((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x)))))))))+(((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x)))))))))))+(((((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x)))))))))+(((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x))))))))))))=(boundaryFullPowerDegree43Block21Norm x).val+(boundaryFullPowerDegree43Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree43Block21Norm x).property (boundaryFullPowerDegree43Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block21Norm,boundaryFullPowerDegree43Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree43Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 43 x=c} := by

  have he0 : boundaryFullPowerRow77 43 x=((((((((((boundaryRePowerRow77_0 43 x)+(boundaryRePowerRow77_1 43 x)))+(((boundaryRePowerRow77_2 43 x)+(((boundaryRePowerRow77_3 43 x)+(boundaryRePowerRow77_4 43 x)))))))+(((((boundaryRePowerRow77_5 43 x)+(((boundaryRePowerRow77_6 43 x)+(boundaryRePowerRow77_7 43 x)))))+(((boundaryRePowerRow77_8 43 x)+(((boundaryRePowerRow77_9 43 x)+(boundaryRePowerRow77_10 43 x)))))))))+(((((((boundaryRePowerRow77_11 43 x)+(((boundaryRePowerRow77_12 43 x)+(boundaryRePowerRow77_13 43 x)))))+(((boundaryRePowerRow77_14 43 x)+(((boundaryRePowerRow77_15 43 x)+(boundaryRePowerRow77_16 43 x)))))))+(((((boundaryRePowerRow77_17 43 x)+(((boundaryRePowerRow77_18 43 x)+(boundaryRePowerRow77_19 43 x)))))+(((boundaryRePowerRow77_20 43 x)+(((boundaryRePowerRow77_21 43 x)+(boundaryRePowerRow77_22 43 x)))))))))))+(((((((((boundaryImPowerRow77_0 43 x)+(boundaryImPowerRow77_1 43 x)))+(((boundaryImPowerRow77_2 43 x)+(((boundaryImPowerRow77_3 43 x)+(boundaryImPowerRow77_4 43 x)))))))+(((((boundaryImPowerRow77_5 43 x)+(((boundaryImPowerRow77_6 43 x)+(boundaryImPowerRow77_7 43 x)))))+(((boundaryImPowerRow77_8 43 x)+(((boundaryImPowerRow77_9 43 x)+(boundaryImPowerRow77_10 43 x)))))))))+(((((((boundaryImPowerRow77_11 43 x)+(((boundaryImPowerRow77_12 43 x)+(boundaryImPowerRow77_13 43 x)))))+(((boundaryImPowerRow77_14 43 x)+(((boundaryImPowerRow77_15 43 x)+(boundaryImPowerRow77_16 43 x)))))))+(((((boundaryImPowerRow77_17 43 x)+(((boundaryImPowerRow77_18 43 x)+(boundaryImPowerRow77_19 43 x)))))+(((boundaryImPowerRow77_20 43 x)+(((boundaryImPowerRow77_21 43 x)+(boundaryLowPowerRow77 43 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree43Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree43Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
