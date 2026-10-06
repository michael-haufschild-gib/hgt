import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree34Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree34Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x))=c} := by

  have he : ((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x))=(boundaryRePowerRow77_0Degree34Norm x).val+(boundaryRePowerRow77_1Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree34Norm x).property (boundaryRePowerRow77_1Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree34Norm,boundaryRePowerRow77_1Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x))=c} := by

  have he : ((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x))=(boundaryRePowerRow77_3Degree34Norm x).val+(boundaryRePowerRow77_4Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree34Norm x).property (boundaryRePowerRow77_4Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree34Norm,boundaryRePowerRow77_4Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x))))=(boundaryRePowerRow77_2Degree34Norm x).val+(boundaryFullPowerDegree34Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree34Norm x).property (boundaryFullPowerDegree34Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree34Norm,boundaryFullPowerDegree34Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x))))))=(boundaryFullPowerDegree34Block0Norm x).val+(boundaryFullPowerDegree34Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block0Norm x).property (boundaryFullPowerDegree34Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block0Norm,boundaryFullPowerDegree34Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x))=c} := by

  have he : ((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x))=(boundaryRePowerRow77_6Degree34Norm x).val+(boundaryRePowerRow77_7Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree34Norm x).property (boundaryRePowerRow77_7Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree34Norm,boundaryRePowerRow77_7Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x))))=(boundaryRePowerRow77_5Degree34Norm x).val+(boundaryFullPowerDegree34Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree34Norm x).property (boundaryFullPowerDegree34Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree34Norm,boundaryFullPowerDegree34Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))=c} := by

  have he : ((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))=(boundaryRePowerRow77_9Degree34Norm x).val+(boundaryRePowerRow77_10Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree34Norm x).property (boundaryRePowerRow77_10Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree34Norm,boundaryRePowerRow77_10Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))))=(boundaryRePowerRow77_8Degree34Norm x).val+(boundaryFullPowerDegree34Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree34Norm x).property (boundaryFullPowerDegree34Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree34Norm,boundaryFullPowerDegree34Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))))))=(boundaryFullPowerDegree34Block5Norm x).val+(boundaryFullPowerDegree34Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block5Norm x).property (boundaryFullPowerDegree34Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block5Norm,boundaryFullPowerDegree34Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x))))))))=(boundaryFullPowerDegree34Block3Norm x).val+(boundaryFullPowerDegree34Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block3Norm x).property (boundaryFullPowerDegree34Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block3Norm,boundaryFullPowerDegree34Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x))=c} := by

  have he : ((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x))=(boundaryRePowerRow77_12Degree34Norm x).val+(boundaryRePowerRow77_13Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree34Norm x).property (boundaryRePowerRow77_13Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree34Norm,boundaryRePowerRow77_13Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x))))=(boundaryRePowerRow77_11Degree34Norm x).val+(boundaryFullPowerDegree34Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree34Norm x).property (boundaryFullPowerDegree34Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree34Norm,boundaryFullPowerDegree34Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x))=c} := by

  have he : ((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x))=(boundaryRePowerRow77_15Degree34Norm x).val+(boundaryRePowerRow77_16Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree34Norm x).property (boundaryRePowerRow77_16Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree34Norm,boundaryRePowerRow77_16Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x))))=(boundaryRePowerRow77_14Degree34Norm x).val+(boundaryFullPowerDegree34Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree34Norm x).property (boundaryFullPowerDegree34Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree34Norm,boundaryFullPowerDegree34Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x))))))=(boundaryFullPowerDegree34Block11Norm x).val+(boundaryFullPowerDegree34Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block11Norm x).property (boundaryFullPowerDegree34Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block11Norm,boundaryFullPowerDegree34Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x))=c} := by

  have he : ((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x))=(boundaryRePowerRow77_18Degree34Norm x).val+(boundaryRePowerRow77_19Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree34Norm x).property (boundaryRePowerRow77_19Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree34Norm,boundaryRePowerRow77_19Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x))))=(boundaryRePowerRow77_17Degree34Norm x).val+(boundaryFullPowerDegree34Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree34Norm x).property (boundaryFullPowerDegree34Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree34Norm,boundaryFullPowerDegree34Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))=c} := by

  have he : ((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))=(boundaryRePowerRow77_21Degree34Norm x).val+(boundaryRePowerRow77_22Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree34Norm x).property (boundaryRePowerRow77_22Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree34Norm,boundaryRePowerRow77_22Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))=(boundaryRePowerRow77_20Degree34Norm x).val+(boundaryFullPowerDegree34Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree34Norm x).property (boundaryFullPowerDegree34Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree34Norm,boundaryFullPowerDegree34Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))))=(boundaryFullPowerDegree34Block16Norm x).val+(boundaryFullPowerDegree34Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block16Norm x).property (boundaryFullPowerDegree34Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block16Norm,boundaryFullPowerDegree34Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))))))=(boundaryFullPowerDegree34Block14Norm x).val+(boundaryFullPowerDegree34Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block14Norm x).property (boundaryFullPowerDegree34Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block14Norm,boundaryFullPowerDegree34Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x)))))))))+(((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x)))))))))+(((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x))))))))))=(boundaryFullPowerDegree34Block9Norm x).val+(boundaryFullPowerDegree34Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block9Norm x).property (boundaryFullPowerDegree34Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block9Norm,boundaryFullPowerDegree34Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x))=c} := by

  have he : ((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x))=(boundaryImPowerRow77_0Degree34Norm x).val+(boundaryImPowerRow77_1Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree34Norm x).property (boundaryImPowerRow77_1Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree34Norm,boundaryImPowerRow77_1Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x))=c} := by

  have he : ((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x))=(boundaryImPowerRow77_3Degree34Norm x).val+(boundaryImPowerRow77_4Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree34Norm x).property (boundaryImPowerRow77_4Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree34Norm,boundaryImPowerRow77_4Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x))))=(boundaryImPowerRow77_2Degree34Norm x).val+(boundaryFullPowerDegree34Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree34Norm x).property (boundaryFullPowerDegree34Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree34Norm,boundaryFullPowerDegree34Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x))))))=(boundaryFullPowerDegree34Block22Norm x).val+(boundaryFullPowerDegree34Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block22Norm x).property (boundaryFullPowerDegree34Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block22Norm,boundaryFullPowerDegree34Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x))=c} := by

  have he : ((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x))=(boundaryImPowerRow77_6Degree34Norm x).val+(boundaryImPowerRow77_7Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree34Norm x).property (boundaryImPowerRow77_7Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree34Norm,boundaryImPowerRow77_7Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x))))=(boundaryImPowerRow77_5Degree34Norm x).val+(boundaryFullPowerDegree34Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree34Norm x).property (boundaryFullPowerDegree34Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree34Norm,boundaryFullPowerDegree34Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))=c} := by

  have he : ((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))=(boundaryImPowerRow77_9Degree34Norm x).val+(boundaryImPowerRow77_10Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree34Norm x).property (boundaryImPowerRow77_10Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree34Norm,boundaryImPowerRow77_10Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))))=(boundaryImPowerRow77_8Degree34Norm x).val+(boundaryFullPowerDegree34Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree34Norm x).property (boundaryFullPowerDegree34Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree34Norm,boundaryFullPowerDegree34Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))))))=(boundaryFullPowerDegree34Block27Norm x).val+(boundaryFullPowerDegree34Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block27Norm x).property (boundaryFullPowerDegree34Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block27Norm,boundaryFullPowerDegree34Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x))))))))=(boundaryFullPowerDegree34Block25Norm x).val+(boundaryFullPowerDegree34Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block25Norm x).property (boundaryFullPowerDegree34Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block25Norm,boundaryFullPowerDegree34Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x))=c} := by

  have he : ((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x))=(boundaryImPowerRow77_12Degree34Norm x).val+(boundaryImPowerRow77_13Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree34Norm x).property (boundaryImPowerRow77_13Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree34Norm,boundaryImPowerRow77_13Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x))))=(boundaryImPowerRow77_11Degree34Norm x).val+(boundaryFullPowerDegree34Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree34Norm x).property (boundaryFullPowerDegree34Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree34Norm,boundaryFullPowerDegree34Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x))=c} := by

  have he : ((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x))=(boundaryImPowerRow77_15Degree34Norm x).val+(boundaryImPowerRow77_16Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree34Norm x).property (boundaryImPowerRow77_16Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree34Norm,boundaryImPowerRow77_16Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x))))=(boundaryImPowerRow77_14Degree34Norm x).val+(boundaryFullPowerDegree34Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree34Norm x).property (boundaryFullPowerDegree34Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree34Norm,boundaryFullPowerDegree34Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x))))))=(boundaryFullPowerDegree34Block33Norm x).val+(boundaryFullPowerDegree34Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block33Norm x).property (boundaryFullPowerDegree34Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block33Norm,boundaryFullPowerDegree34Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x))=c} := by

  have he : ((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x))=(boundaryImPowerRow77_18Degree34Norm x).val+(boundaryImPowerRow77_19Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree34Norm x).property (boundaryImPowerRow77_19Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree34Norm,boundaryImPowerRow77_19Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x))))=(boundaryImPowerRow77_17Degree34Norm x).val+(boundaryFullPowerDegree34Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree34Norm x).property (boundaryFullPowerDegree34Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree34Norm,boundaryFullPowerDegree34Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))=c} := by

  have he : ((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))=(boundaryImPowerRow77_21Degree34Norm x).val+(boundaryLowPowerRow77Degree34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree34Norm x).property (boundaryLowPowerRow77Degree34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree34Norm,boundaryLowPowerRow77Degree34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))=(boundaryImPowerRow77_20Degree34Norm x).val+(boundaryFullPowerDegree34Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree34Norm x).property (boundaryFullPowerDegree34Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree34Norm,boundaryFullPowerDegree34Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))=(boundaryFullPowerDegree34Block38Norm x).val+(boundaryFullPowerDegree34Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block38Norm x).property (boundaryFullPowerDegree34Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block38Norm,boundaryFullPowerDegree34Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))))=(boundaryFullPowerDegree34Block36Norm x).val+(boundaryFullPowerDegree34Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block36Norm x).property (boundaryFullPowerDegree34Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block36Norm,boundaryFullPowerDegree34Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x)))))))))+(((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x)))))))))+(((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))))))=(boundaryFullPowerDegree34Block31Norm x).val+(boundaryFullPowerDegree34Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block31Norm x).property (boundaryFullPowerDegree34Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block31Norm,boundaryFullPowerDegree34Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree34Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x)))))))))+(((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x)))))))))))+(((((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x)))))))))+(((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x)))))))))+(((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x)))))))))))+(((((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x)))))))))+(((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x))))))))))))=(boundaryFullPowerDegree34Block21Norm x).val+(boundaryFullPowerDegree34Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree34Block21Norm x).property (boundaryFullPowerDegree34Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block21Norm,boundaryFullPowerDegree34Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree34Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 34 x=c} := by

  have he0 : boundaryFullPowerRow77 34 x=((((((((((boundaryRePowerRow77_0 34 x)+(boundaryRePowerRow77_1 34 x)))+(((boundaryRePowerRow77_2 34 x)+(((boundaryRePowerRow77_3 34 x)+(boundaryRePowerRow77_4 34 x)))))))+(((((boundaryRePowerRow77_5 34 x)+(((boundaryRePowerRow77_6 34 x)+(boundaryRePowerRow77_7 34 x)))))+(((boundaryRePowerRow77_8 34 x)+(((boundaryRePowerRow77_9 34 x)+(boundaryRePowerRow77_10 34 x)))))))))+(((((((boundaryRePowerRow77_11 34 x)+(((boundaryRePowerRow77_12 34 x)+(boundaryRePowerRow77_13 34 x)))))+(((boundaryRePowerRow77_14 34 x)+(((boundaryRePowerRow77_15 34 x)+(boundaryRePowerRow77_16 34 x)))))))+(((((boundaryRePowerRow77_17 34 x)+(((boundaryRePowerRow77_18 34 x)+(boundaryRePowerRow77_19 34 x)))))+(((boundaryRePowerRow77_20 34 x)+(((boundaryRePowerRow77_21 34 x)+(boundaryRePowerRow77_22 34 x)))))))))))+(((((((((boundaryImPowerRow77_0 34 x)+(boundaryImPowerRow77_1 34 x)))+(((boundaryImPowerRow77_2 34 x)+(((boundaryImPowerRow77_3 34 x)+(boundaryImPowerRow77_4 34 x)))))))+(((((boundaryImPowerRow77_5 34 x)+(((boundaryImPowerRow77_6 34 x)+(boundaryImPowerRow77_7 34 x)))))+(((boundaryImPowerRow77_8 34 x)+(((boundaryImPowerRow77_9 34 x)+(boundaryImPowerRow77_10 34 x)))))))))+(((((((boundaryImPowerRow77_11 34 x)+(((boundaryImPowerRow77_12 34 x)+(boundaryImPowerRow77_13 34 x)))))+(((boundaryImPowerRow77_14 34 x)+(((boundaryImPowerRow77_15 34 x)+(boundaryImPowerRow77_16 34 x)))))))+(((((boundaryImPowerRow77_17 34 x)+(((boundaryImPowerRow77_18 34 x)+(boundaryImPowerRow77_19 34 x)))))+(((boundaryImPowerRow77_20 34 x)+(((boundaryImPowerRow77_21 34 x)+(boundaryLowPowerRow77 34 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree34Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree34Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
