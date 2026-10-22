import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree7Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree7Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x))=c} := by

  have he : ((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x))=(boundaryRePowerRow77_0Degree7Norm x).val+(boundaryRePowerRow77_1Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree7Norm x).property (boundaryRePowerRow77_1Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree7Norm,boundaryRePowerRow77_1Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x))=c} := by

  have he : ((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x))=(boundaryRePowerRow77_3Degree7Norm x).val+(boundaryRePowerRow77_4Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree7Norm x).property (boundaryRePowerRow77_4Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree7Norm,boundaryRePowerRow77_4Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x))))=(boundaryRePowerRow77_2Degree7Norm x).val+(boundaryFullPowerDegree7Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree7Norm x).property (boundaryFullPowerDegree7Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree7Norm,boundaryFullPowerDegree7Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x))))))=(boundaryFullPowerDegree7Block0Norm x).val+(boundaryFullPowerDegree7Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block0Norm x).property (boundaryFullPowerDegree7Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block0Norm,boundaryFullPowerDegree7Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x))=c} := by

  have he : ((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x))=(boundaryRePowerRow77_6Degree7Norm x).val+(boundaryRePowerRow77_7Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree7Norm x).property (boundaryRePowerRow77_7Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree7Norm,boundaryRePowerRow77_7Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x))))=(boundaryRePowerRow77_5Degree7Norm x).val+(boundaryFullPowerDegree7Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree7Norm x).property (boundaryFullPowerDegree7Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree7Norm,boundaryFullPowerDegree7Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))=c} := by

  have he : ((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))=(boundaryRePowerRow77_9Degree7Norm x).val+(boundaryRePowerRow77_10Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree7Norm x).property (boundaryRePowerRow77_10Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree7Norm,boundaryRePowerRow77_10Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))))=(boundaryRePowerRow77_8Degree7Norm x).val+(boundaryFullPowerDegree7Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree7Norm x).property (boundaryFullPowerDegree7Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree7Norm,boundaryFullPowerDegree7Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))))))=(boundaryFullPowerDegree7Block5Norm x).val+(boundaryFullPowerDegree7Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block5Norm x).property (boundaryFullPowerDegree7Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block5Norm,boundaryFullPowerDegree7Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x))))))))=(boundaryFullPowerDegree7Block3Norm x).val+(boundaryFullPowerDegree7Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block3Norm x).property (boundaryFullPowerDegree7Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block3Norm,boundaryFullPowerDegree7Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x))=c} := by

  have he : ((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x))=(boundaryRePowerRow77_12Degree7Norm x).val+(boundaryRePowerRow77_13Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree7Norm x).property (boundaryRePowerRow77_13Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree7Norm,boundaryRePowerRow77_13Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x))))=(boundaryRePowerRow77_11Degree7Norm x).val+(boundaryFullPowerDegree7Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree7Norm x).property (boundaryFullPowerDegree7Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree7Norm,boundaryFullPowerDegree7Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x))=c} := by

  have he : ((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x))=(boundaryRePowerRow77_15Degree7Norm x).val+(boundaryRePowerRow77_16Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree7Norm x).property (boundaryRePowerRow77_16Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree7Norm,boundaryRePowerRow77_16Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x))))=(boundaryRePowerRow77_14Degree7Norm x).val+(boundaryFullPowerDegree7Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree7Norm x).property (boundaryFullPowerDegree7Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree7Norm,boundaryFullPowerDegree7Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x))))))=(boundaryFullPowerDegree7Block11Norm x).val+(boundaryFullPowerDegree7Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block11Norm x).property (boundaryFullPowerDegree7Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block11Norm,boundaryFullPowerDegree7Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x))=c} := by

  have he : ((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x))=(boundaryRePowerRow77_18Degree7Norm x).val+(boundaryRePowerRow77_19Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree7Norm x).property (boundaryRePowerRow77_19Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree7Norm,boundaryRePowerRow77_19Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x))))=(boundaryRePowerRow77_17Degree7Norm x).val+(boundaryFullPowerDegree7Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree7Norm x).property (boundaryFullPowerDegree7Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree7Norm,boundaryFullPowerDegree7Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))=c} := by

  have he : ((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))=(boundaryRePowerRow77_21Degree7Norm x).val+(boundaryRePowerRow77_22Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree7Norm x).property (boundaryRePowerRow77_22Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree7Norm,boundaryRePowerRow77_22Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))=(boundaryRePowerRow77_20Degree7Norm x).val+(boundaryFullPowerDegree7Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree7Norm x).property (boundaryFullPowerDegree7Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree7Norm,boundaryFullPowerDegree7Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))))=(boundaryFullPowerDegree7Block16Norm x).val+(boundaryFullPowerDegree7Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block16Norm x).property (boundaryFullPowerDegree7Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block16Norm,boundaryFullPowerDegree7Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))))))=(boundaryFullPowerDegree7Block14Norm x).val+(boundaryFullPowerDegree7Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block14Norm x).property (boundaryFullPowerDegree7Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block14Norm,boundaryFullPowerDegree7Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x)))))))))+(((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x)))))))))+(((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x))))))))))=(boundaryFullPowerDegree7Block9Norm x).val+(boundaryFullPowerDegree7Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block9Norm x).property (boundaryFullPowerDegree7Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block9Norm,boundaryFullPowerDegree7Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x))=c} := by

  have he : ((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x))=(boundaryImPowerRow77_0Degree7Norm x).val+(boundaryImPowerRow77_1Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree7Norm x).property (boundaryImPowerRow77_1Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree7Norm,boundaryImPowerRow77_1Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x))=c} := by

  have he : ((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x))=(boundaryImPowerRow77_3Degree7Norm x).val+(boundaryImPowerRow77_4Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree7Norm x).property (boundaryImPowerRow77_4Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree7Norm,boundaryImPowerRow77_4Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x))))=(boundaryImPowerRow77_2Degree7Norm x).val+(boundaryFullPowerDegree7Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree7Norm x).property (boundaryFullPowerDegree7Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree7Norm,boundaryFullPowerDegree7Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x))))))=(boundaryFullPowerDegree7Block22Norm x).val+(boundaryFullPowerDegree7Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block22Norm x).property (boundaryFullPowerDegree7Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block22Norm,boundaryFullPowerDegree7Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x))=c} := by

  have he : ((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x))=(boundaryImPowerRow77_6Degree7Norm x).val+(boundaryImPowerRow77_7Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree7Norm x).property (boundaryImPowerRow77_7Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree7Norm,boundaryImPowerRow77_7Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x))))=(boundaryImPowerRow77_5Degree7Norm x).val+(boundaryFullPowerDegree7Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree7Norm x).property (boundaryFullPowerDegree7Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree7Norm,boundaryFullPowerDegree7Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))=c} := by

  have he : ((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))=(boundaryImPowerRow77_9Degree7Norm x).val+(boundaryImPowerRow77_10Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree7Norm x).property (boundaryImPowerRow77_10Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree7Norm,boundaryImPowerRow77_10Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))))=(boundaryImPowerRow77_8Degree7Norm x).val+(boundaryFullPowerDegree7Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree7Norm x).property (boundaryFullPowerDegree7Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree7Norm,boundaryFullPowerDegree7Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))))))=(boundaryFullPowerDegree7Block27Norm x).val+(boundaryFullPowerDegree7Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block27Norm x).property (boundaryFullPowerDegree7Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block27Norm,boundaryFullPowerDegree7Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x))))))))=(boundaryFullPowerDegree7Block25Norm x).val+(boundaryFullPowerDegree7Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block25Norm x).property (boundaryFullPowerDegree7Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block25Norm,boundaryFullPowerDegree7Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x))=c} := by

  have he : ((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x))=(boundaryImPowerRow77_12Degree7Norm x).val+(boundaryImPowerRow77_13Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree7Norm x).property (boundaryImPowerRow77_13Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree7Norm,boundaryImPowerRow77_13Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x))))=(boundaryImPowerRow77_11Degree7Norm x).val+(boundaryFullPowerDegree7Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree7Norm x).property (boundaryFullPowerDegree7Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree7Norm,boundaryFullPowerDegree7Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x))=c} := by

  have he : ((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x))=(boundaryImPowerRow77_15Degree7Norm x).val+(boundaryImPowerRow77_16Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree7Norm x).property (boundaryImPowerRow77_16Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree7Norm,boundaryImPowerRow77_16Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x))))=(boundaryImPowerRow77_14Degree7Norm x).val+(boundaryFullPowerDegree7Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree7Norm x).property (boundaryFullPowerDegree7Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree7Norm,boundaryFullPowerDegree7Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x))))))=(boundaryFullPowerDegree7Block33Norm x).val+(boundaryFullPowerDegree7Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block33Norm x).property (boundaryFullPowerDegree7Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block33Norm,boundaryFullPowerDegree7Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x))=c} := by

  have he : ((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x))=(boundaryImPowerRow77_18Degree7Norm x).val+(boundaryImPowerRow77_19Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree7Norm x).property (boundaryImPowerRow77_19Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree7Norm,boundaryImPowerRow77_19Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x))))=(boundaryImPowerRow77_17Degree7Norm x).val+(boundaryFullPowerDegree7Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree7Norm x).property (boundaryFullPowerDegree7Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree7Norm,boundaryFullPowerDegree7Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))=c} := by

  have he : ((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))=(boundaryImPowerRow77_21Degree7Norm x).val+(boundaryLowPowerRow77Degree7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree7Norm x).property (boundaryLowPowerRow77Degree7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree7Norm,boundaryLowPowerRow77Degree7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))=(boundaryImPowerRow77_20Degree7Norm x).val+(boundaryFullPowerDegree7Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree7Norm x).property (boundaryFullPowerDegree7Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree7Norm,boundaryFullPowerDegree7Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))=(boundaryFullPowerDegree7Block38Norm x).val+(boundaryFullPowerDegree7Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block38Norm x).property (boundaryFullPowerDegree7Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block38Norm,boundaryFullPowerDegree7Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))))=(boundaryFullPowerDegree7Block36Norm x).val+(boundaryFullPowerDegree7Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block36Norm x).property (boundaryFullPowerDegree7Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block36Norm,boundaryFullPowerDegree7Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x)))))))))+(((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x)))))))))+(((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))))))=(boundaryFullPowerDegree7Block31Norm x).val+(boundaryFullPowerDegree7Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block31Norm x).property (boundaryFullPowerDegree7Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block31Norm,boundaryFullPowerDegree7Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree7Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x)))))))))+(((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x)))))))))))+(((((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x)))))))))+(((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x)))))))))+(((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x)))))))))))+(((((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x)))))))))+(((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x))))))))))))=(boundaryFullPowerDegree7Block21Norm x).val+(boundaryFullPowerDegree7Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree7Block21Norm x).property (boundaryFullPowerDegree7Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block21Norm,boundaryFullPowerDegree7Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree7Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 7 x=c} := by

  have he0 : boundaryFullPowerRow77 7 x=((((((((((boundaryRePowerRow77_0 7 x)+(boundaryRePowerRow77_1 7 x)))+(((boundaryRePowerRow77_2 7 x)+(((boundaryRePowerRow77_3 7 x)+(boundaryRePowerRow77_4 7 x)))))))+(((((boundaryRePowerRow77_5 7 x)+(((boundaryRePowerRow77_6 7 x)+(boundaryRePowerRow77_7 7 x)))))+(((boundaryRePowerRow77_8 7 x)+(((boundaryRePowerRow77_9 7 x)+(boundaryRePowerRow77_10 7 x)))))))))+(((((((boundaryRePowerRow77_11 7 x)+(((boundaryRePowerRow77_12 7 x)+(boundaryRePowerRow77_13 7 x)))))+(((boundaryRePowerRow77_14 7 x)+(((boundaryRePowerRow77_15 7 x)+(boundaryRePowerRow77_16 7 x)))))))+(((((boundaryRePowerRow77_17 7 x)+(((boundaryRePowerRow77_18 7 x)+(boundaryRePowerRow77_19 7 x)))))+(((boundaryRePowerRow77_20 7 x)+(((boundaryRePowerRow77_21 7 x)+(boundaryRePowerRow77_22 7 x)))))))))))+(((((((((boundaryImPowerRow77_0 7 x)+(boundaryImPowerRow77_1 7 x)))+(((boundaryImPowerRow77_2 7 x)+(((boundaryImPowerRow77_3 7 x)+(boundaryImPowerRow77_4 7 x)))))))+(((((boundaryImPowerRow77_5 7 x)+(((boundaryImPowerRow77_6 7 x)+(boundaryImPowerRow77_7 7 x)))))+(((boundaryImPowerRow77_8 7 x)+(((boundaryImPowerRow77_9 7 x)+(boundaryImPowerRow77_10 7 x)))))))))+(((((((boundaryImPowerRow77_11 7 x)+(((boundaryImPowerRow77_12 7 x)+(boundaryImPowerRow77_13 7 x)))))+(((boundaryImPowerRow77_14 7 x)+(((boundaryImPowerRow77_15 7 x)+(boundaryImPowerRow77_16 7 x)))))))+(((((boundaryImPowerRow77_17 7 x)+(((boundaryImPowerRow77_18 7 x)+(boundaryImPowerRow77_19 7 x)))))+(((boundaryImPowerRow77_20 7 x)+(((boundaryImPowerRow77_21 7 x)+(boundaryLowPowerRow77 7 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree7Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree7Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
