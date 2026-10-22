import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree65Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree65Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x))=c} := by

  have he : ((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x))=(boundaryRePowerRow77_0Degree65Norm x).val+(boundaryRePowerRow77_1Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree65Norm x).property (boundaryRePowerRow77_1Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree65Norm,boundaryRePowerRow77_1Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x))=c} := by

  have he : ((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x))=(boundaryRePowerRow77_3Degree65Norm x).val+(boundaryRePowerRow77_4Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree65Norm x).property (boundaryRePowerRow77_4Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree65Norm,boundaryRePowerRow77_4Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x))))=(boundaryRePowerRow77_2Degree65Norm x).val+(boundaryFullPowerDegree65Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree65Norm x).property (boundaryFullPowerDegree65Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree65Norm,boundaryFullPowerDegree65Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x))))))=(boundaryFullPowerDegree65Block0Norm x).val+(boundaryFullPowerDegree65Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block0Norm x).property (boundaryFullPowerDegree65Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block0Norm,boundaryFullPowerDegree65Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x))=c} := by

  have he : ((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x))=(boundaryRePowerRow77_6Degree65Norm x).val+(boundaryRePowerRow77_7Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree65Norm x).property (boundaryRePowerRow77_7Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree65Norm,boundaryRePowerRow77_7Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x))))=(boundaryRePowerRow77_5Degree65Norm x).val+(boundaryFullPowerDegree65Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree65Norm x).property (boundaryFullPowerDegree65Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree65Norm,boundaryFullPowerDegree65Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))=c} := by

  have he : ((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))=(boundaryRePowerRow77_9Degree65Norm x).val+(boundaryRePowerRow77_10Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree65Norm x).property (boundaryRePowerRow77_10Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree65Norm,boundaryRePowerRow77_10Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))))=(boundaryRePowerRow77_8Degree65Norm x).val+(boundaryFullPowerDegree65Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree65Norm x).property (boundaryFullPowerDegree65Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree65Norm,boundaryFullPowerDegree65Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))))))=(boundaryFullPowerDegree65Block5Norm x).val+(boundaryFullPowerDegree65Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block5Norm x).property (boundaryFullPowerDegree65Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block5Norm,boundaryFullPowerDegree65Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x))))))))=(boundaryFullPowerDegree65Block3Norm x).val+(boundaryFullPowerDegree65Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block3Norm x).property (boundaryFullPowerDegree65Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block3Norm,boundaryFullPowerDegree65Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x))=c} := by

  have he : ((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x))=(boundaryRePowerRow77_12Degree65Norm x).val+(boundaryRePowerRow77_13Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree65Norm x).property (boundaryRePowerRow77_13Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree65Norm,boundaryRePowerRow77_13Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x))))=(boundaryRePowerRow77_11Degree65Norm x).val+(boundaryFullPowerDegree65Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree65Norm x).property (boundaryFullPowerDegree65Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree65Norm,boundaryFullPowerDegree65Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x))=c} := by

  have he : ((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x))=(boundaryRePowerRow77_15Degree65Norm x).val+(boundaryRePowerRow77_16Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree65Norm x).property (boundaryRePowerRow77_16Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree65Norm,boundaryRePowerRow77_16Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x))))=(boundaryRePowerRow77_14Degree65Norm x).val+(boundaryFullPowerDegree65Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree65Norm x).property (boundaryFullPowerDegree65Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree65Norm,boundaryFullPowerDegree65Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x))))))=(boundaryFullPowerDegree65Block11Norm x).val+(boundaryFullPowerDegree65Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block11Norm x).property (boundaryFullPowerDegree65Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block11Norm,boundaryFullPowerDegree65Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x))=c} := by

  have he : ((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x))=(boundaryRePowerRow77_18Degree65Norm x).val+(boundaryRePowerRow77_19Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree65Norm x).property (boundaryRePowerRow77_19Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree65Norm,boundaryRePowerRow77_19Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x))))=(boundaryRePowerRow77_17Degree65Norm x).val+(boundaryFullPowerDegree65Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree65Norm x).property (boundaryFullPowerDegree65Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree65Norm,boundaryFullPowerDegree65Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))=c} := by

  have he : ((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))=(boundaryRePowerRow77_21Degree65Norm x).val+(boundaryRePowerRow77_22Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree65Norm x).property (boundaryRePowerRow77_22Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree65Norm,boundaryRePowerRow77_22Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))=(boundaryRePowerRow77_20Degree65Norm x).val+(boundaryFullPowerDegree65Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree65Norm x).property (boundaryFullPowerDegree65Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree65Norm,boundaryFullPowerDegree65Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))))=(boundaryFullPowerDegree65Block16Norm x).val+(boundaryFullPowerDegree65Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block16Norm x).property (boundaryFullPowerDegree65Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block16Norm,boundaryFullPowerDegree65Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))))))=(boundaryFullPowerDegree65Block14Norm x).val+(boundaryFullPowerDegree65Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block14Norm x).property (boundaryFullPowerDegree65Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block14Norm,boundaryFullPowerDegree65Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x)))))))))+(((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x)))))))))+(((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x))))))))))=(boundaryFullPowerDegree65Block9Norm x).val+(boundaryFullPowerDegree65Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block9Norm x).property (boundaryFullPowerDegree65Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block9Norm,boundaryFullPowerDegree65Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x))=c} := by

  have he : ((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x))=(boundaryImPowerRow77_0Degree65Norm x).val+(boundaryImPowerRow77_1Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree65Norm x).property (boundaryImPowerRow77_1Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree65Norm,boundaryImPowerRow77_1Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x))=c} := by

  have he : ((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x))=(boundaryImPowerRow77_3Degree65Norm x).val+(boundaryImPowerRow77_4Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree65Norm x).property (boundaryImPowerRow77_4Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree65Norm,boundaryImPowerRow77_4Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x))))=(boundaryImPowerRow77_2Degree65Norm x).val+(boundaryFullPowerDegree65Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree65Norm x).property (boundaryFullPowerDegree65Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree65Norm,boundaryFullPowerDegree65Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x))))))=(boundaryFullPowerDegree65Block22Norm x).val+(boundaryFullPowerDegree65Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block22Norm x).property (boundaryFullPowerDegree65Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block22Norm,boundaryFullPowerDegree65Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x))=c} := by

  have he : ((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x))=(boundaryImPowerRow77_6Degree65Norm x).val+(boundaryImPowerRow77_7Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree65Norm x).property (boundaryImPowerRow77_7Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree65Norm,boundaryImPowerRow77_7Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x))))=(boundaryImPowerRow77_5Degree65Norm x).val+(boundaryFullPowerDegree65Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree65Norm x).property (boundaryFullPowerDegree65Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree65Norm,boundaryFullPowerDegree65Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))=c} := by

  have he : ((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))=(boundaryImPowerRow77_9Degree65Norm x).val+(boundaryImPowerRow77_10Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree65Norm x).property (boundaryImPowerRow77_10Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree65Norm,boundaryImPowerRow77_10Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))))=(boundaryImPowerRow77_8Degree65Norm x).val+(boundaryFullPowerDegree65Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree65Norm x).property (boundaryFullPowerDegree65Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree65Norm,boundaryFullPowerDegree65Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))))))=(boundaryFullPowerDegree65Block27Norm x).val+(boundaryFullPowerDegree65Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block27Norm x).property (boundaryFullPowerDegree65Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block27Norm,boundaryFullPowerDegree65Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x))))))))=(boundaryFullPowerDegree65Block25Norm x).val+(boundaryFullPowerDegree65Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block25Norm x).property (boundaryFullPowerDegree65Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block25Norm,boundaryFullPowerDegree65Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x))=c} := by

  have he : ((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x))=(boundaryImPowerRow77_12Degree65Norm x).val+(boundaryImPowerRow77_13Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree65Norm x).property (boundaryImPowerRow77_13Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree65Norm,boundaryImPowerRow77_13Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x))))=(boundaryImPowerRow77_11Degree65Norm x).val+(boundaryFullPowerDegree65Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree65Norm x).property (boundaryFullPowerDegree65Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree65Norm,boundaryFullPowerDegree65Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x))=c} := by

  have he : ((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x))=(boundaryImPowerRow77_15Degree65Norm x).val+(boundaryImPowerRow77_16Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree65Norm x).property (boundaryImPowerRow77_16Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree65Norm,boundaryImPowerRow77_16Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x))))=(boundaryImPowerRow77_14Degree65Norm x).val+(boundaryFullPowerDegree65Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree65Norm x).property (boundaryFullPowerDegree65Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree65Norm,boundaryFullPowerDegree65Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x))))))=(boundaryFullPowerDegree65Block33Norm x).val+(boundaryFullPowerDegree65Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block33Norm x).property (boundaryFullPowerDegree65Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block33Norm,boundaryFullPowerDegree65Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x))=c} := by

  have he : ((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x))=(boundaryImPowerRow77_18Degree65Norm x).val+(boundaryImPowerRow77_19Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree65Norm x).property (boundaryImPowerRow77_19Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree65Norm,boundaryImPowerRow77_19Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x))))=(boundaryImPowerRow77_17Degree65Norm x).val+(boundaryFullPowerDegree65Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree65Norm x).property (boundaryFullPowerDegree65Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree65Norm,boundaryFullPowerDegree65Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))=c} := by

  have he : ((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))=(boundaryImPowerRow77_21Degree65Norm x).val+(boundaryLowPowerRow77Degree65Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree65Norm x).property (boundaryLowPowerRow77Degree65Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree65Norm,boundaryLowPowerRow77Degree65Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))=(boundaryImPowerRow77_20Degree65Norm x).val+(boundaryFullPowerDegree65Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree65Norm x).property (boundaryFullPowerDegree65Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree65Norm,boundaryFullPowerDegree65Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))=(boundaryFullPowerDegree65Block38Norm x).val+(boundaryFullPowerDegree65Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block38Norm x).property (boundaryFullPowerDegree65Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block38Norm,boundaryFullPowerDegree65Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))))=(boundaryFullPowerDegree65Block36Norm x).val+(boundaryFullPowerDegree65Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block36Norm x).property (boundaryFullPowerDegree65Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block36Norm,boundaryFullPowerDegree65Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x)))))))))+(((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x)))))))))+(((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))))))=(boundaryFullPowerDegree65Block31Norm x).val+(boundaryFullPowerDegree65Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block31Norm x).property (boundaryFullPowerDegree65Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block31Norm,boundaryFullPowerDegree65Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree65Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x)))))))))+(((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x)))))))))))+(((((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x)))))))))+(((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x)))))))))+(((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x)))))))))))+(((((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x)))))))))+(((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x))))))))))))=(boundaryFullPowerDegree65Block21Norm x).val+(boundaryFullPowerDegree65Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree65Block21Norm x).property (boundaryFullPowerDegree65Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block21Norm,boundaryFullPowerDegree65Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree65Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 65 x=c} := by

  have he0 : boundaryFullPowerRow77 65 x=((((((((((boundaryRePowerRow77_0 65 x)+(boundaryRePowerRow77_1 65 x)))+(((boundaryRePowerRow77_2 65 x)+(((boundaryRePowerRow77_3 65 x)+(boundaryRePowerRow77_4 65 x)))))))+(((((boundaryRePowerRow77_5 65 x)+(((boundaryRePowerRow77_6 65 x)+(boundaryRePowerRow77_7 65 x)))))+(((boundaryRePowerRow77_8 65 x)+(((boundaryRePowerRow77_9 65 x)+(boundaryRePowerRow77_10 65 x)))))))))+(((((((boundaryRePowerRow77_11 65 x)+(((boundaryRePowerRow77_12 65 x)+(boundaryRePowerRow77_13 65 x)))))+(((boundaryRePowerRow77_14 65 x)+(((boundaryRePowerRow77_15 65 x)+(boundaryRePowerRow77_16 65 x)))))))+(((((boundaryRePowerRow77_17 65 x)+(((boundaryRePowerRow77_18 65 x)+(boundaryRePowerRow77_19 65 x)))))+(((boundaryRePowerRow77_20 65 x)+(((boundaryRePowerRow77_21 65 x)+(boundaryRePowerRow77_22 65 x)))))))))))+(((((((((boundaryImPowerRow77_0 65 x)+(boundaryImPowerRow77_1 65 x)))+(((boundaryImPowerRow77_2 65 x)+(((boundaryImPowerRow77_3 65 x)+(boundaryImPowerRow77_4 65 x)))))))+(((((boundaryImPowerRow77_5 65 x)+(((boundaryImPowerRow77_6 65 x)+(boundaryImPowerRow77_7 65 x)))))+(((boundaryImPowerRow77_8 65 x)+(((boundaryImPowerRow77_9 65 x)+(boundaryImPowerRow77_10 65 x)))))))))+(((((((boundaryImPowerRow77_11 65 x)+(((boundaryImPowerRow77_12 65 x)+(boundaryImPowerRow77_13 65 x)))))+(((boundaryImPowerRow77_14 65 x)+(((boundaryImPowerRow77_15 65 x)+(boundaryImPowerRow77_16 65 x)))))))+(((((boundaryImPowerRow77_17 65 x)+(((boundaryImPowerRow77_18 65 x)+(boundaryImPowerRow77_19 65 x)))))+(((boundaryImPowerRow77_20 65 x)+(((boundaryImPowerRow77_21 65 x)+(boundaryLowPowerRow77 65 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree65Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree65Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
