import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree66Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree66Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x))=c} := by

  have he : ((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x))=(boundaryRePowerRow77_0Degree66Norm x).val+(boundaryRePowerRow77_1Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree66Norm x).property (boundaryRePowerRow77_1Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree66Norm,boundaryRePowerRow77_1Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x))=c} := by

  have he : ((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x))=(boundaryRePowerRow77_3Degree66Norm x).val+(boundaryRePowerRow77_4Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree66Norm x).property (boundaryRePowerRow77_4Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree66Norm,boundaryRePowerRow77_4Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x))))=(boundaryRePowerRow77_2Degree66Norm x).val+(boundaryFullPowerDegree66Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree66Norm x).property (boundaryFullPowerDegree66Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree66Norm,boundaryFullPowerDegree66Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x))))))=(boundaryFullPowerDegree66Block0Norm x).val+(boundaryFullPowerDegree66Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block0Norm x).property (boundaryFullPowerDegree66Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block0Norm,boundaryFullPowerDegree66Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x))=c} := by

  have he : ((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x))=(boundaryRePowerRow77_6Degree66Norm x).val+(boundaryRePowerRow77_7Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree66Norm x).property (boundaryRePowerRow77_7Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree66Norm,boundaryRePowerRow77_7Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x))))=(boundaryRePowerRow77_5Degree66Norm x).val+(boundaryFullPowerDegree66Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree66Norm x).property (boundaryFullPowerDegree66Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree66Norm,boundaryFullPowerDegree66Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))=c} := by

  have he : ((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))=(boundaryRePowerRow77_9Degree66Norm x).val+(boundaryRePowerRow77_10Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree66Norm x).property (boundaryRePowerRow77_10Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree66Norm,boundaryRePowerRow77_10Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))))=(boundaryRePowerRow77_8Degree66Norm x).val+(boundaryFullPowerDegree66Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree66Norm x).property (boundaryFullPowerDegree66Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree66Norm,boundaryFullPowerDegree66Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))))))=(boundaryFullPowerDegree66Block5Norm x).val+(boundaryFullPowerDegree66Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block5Norm x).property (boundaryFullPowerDegree66Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block5Norm,boundaryFullPowerDegree66Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x))))))))=(boundaryFullPowerDegree66Block3Norm x).val+(boundaryFullPowerDegree66Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block3Norm x).property (boundaryFullPowerDegree66Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block3Norm,boundaryFullPowerDegree66Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x))=c} := by

  have he : ((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x))=(boundaryRePowerRow77_12Degree66Norm x).val+(boundaryRePowerRow77_13Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree66Norm x).property (boundaryRePowerRow77_13Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree66Norm,boundaryRePowerRow77_13Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x))))=(boundaryRePowerRow77_11Degree66Norm x).val+(boundaryFullPowerDegree66Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree66Norm x).property (boundaryFullPowerDegree66Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree66Norm,boundaryFullPowerDegree66Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x))=c} := by

  have he : ((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x))=(boundaryRePowerRow77_15Degree66Norm x).val+(boundaryRePowerRow77_16Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree66Norm x).property (boundaryRePowerRow77_16Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree66Norm,boundaryRePowerRow77_16Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x))))=(boundaryRePowerRow77_14Degree66Norm x).val+(boundaryFullPowerDegree66Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree66Norm x).property (boundaryFullPowerDegree66Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree66Norm,boundaryFullPowerDegree66Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x))))))=(boundaryFullPowerDegree66Block11Norm x).val+(boundaryFullPowerDegree66Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block11Norm x).property (boundaryFullPowerDegree66Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block11Norm,boundaryFullPowerDegree66Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x))=c} := by

  have he : ((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x))=(boundaryRePowerRow77_18Degree66Norm x).val+(boundaryRePowerRow77_19Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree66Norm x).property (boundaryRePowerRow77_19Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree66Norm,boundaryRePowerRow77_19Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x))))=(boundaryRePowerRow77_17Degree66Norm x).val+(boundaryFullPowerDegree66Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree66Norm x).property (boundaryFullPowerDegree66Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree66Norm,boundaryFullPowerDegree66Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))=c} := by

  have he : ((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))=(boundaryRePowerRow77_21Degree66Norm x).val+(boundaryRePowerRow77_22Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree66Norm x).property (boundaryRePowerRow77_22Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree66Norm,boundaryRePowerRow77_22Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))=(boundaryRePowerRow77_20Degree66Norm x).val+(boundaryFullPowerDegree66Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree66Norm x).property (boundaryFullPowerDegree66Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree66Norm,boundaryFullPowerDegree66Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))))=(boundaryFullPowerDegree66Block16Norm x).val+(boundaryFullPowerDegree66Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block16Norm x).property (boundaryFullPowerDegree66Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block16Norm,boundaryFullPowerDegree66Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))))))=(boundaryFullPowerDegree66Block14Norm x).val+(boundaryFullPowerDegree66Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block14Norm x).property (boundaryFullPowerDegree66Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block14Norm,boundaryFullPowerDegree66Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x)))))))))+(((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x)))))))))+(((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x))))))))))=(boundaryFullPowerDegree66Block9Norm x).val+(boundaryFullPowerDegree66Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block9Norm x).property (boundaryFullPowerDegree66Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block9Norm,boundaryFullPowerDegree66Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x))=c} := by

  have he : ((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x))=(boundaryImPowerRow77_0Degree66Norm x).val+(boundaryImPowerRow77_1Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree66Norm x).property (boundaryImPowerRow77_1Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree66Norm,boundaryImPowerRow77_1Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x))=c} := by

  have he : ((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x))=(boundaryImPowerRow77_3Degree66Norm x).val+(boundaryImPowerRow77_4Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree66Norm x).property (boundaryImPowerRow77_4Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree66Norm,boundaryImPowerRow77_4Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x))))=(boundaryImPowerRow77_2Degree66Norm x).val+(boundaryFullPowerDegree66Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree66Norm x).property (boundaryFullPowerDegree66Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree66Norm,boundaryFullPowerDegree66Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x))))))=(boundaryFullPowerDegree66Block22Norm x).val+(boundaryFullPowerDegree66Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block22Norm x).property (boundaryFullPowerDegree66Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block22Norm,boundaryFullPowerDegree66Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x))=c} := by

  have he : ((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x))=(boundaryImPowerRow77_6Degree66Norm x).val+(boundaryImPowerRow77_7Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree66Norm x).property (boundaryImPowerRow77_7Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree66Norm,boundaryImPowerRow77_7Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x))))=(boundaryImPowerRow77_5Degree66Norm x).val+(boundaryFullPowerDegree66Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree66Norm x).property (boundaryFullPowerDegree66Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree66Norm,boundaryFullPowerDegree66Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))=c} := by

  have he : ((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))=(boundaryImPowerRow77_9Degree66Norm x).val+(boundaryImPowerRow77_10Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree66Norm x).property (boundaryImPowerRow77_10Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree66Norm,boundaryImPowerRow77_10Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))))=(boundaryImPowerRow77_8Degree66Norm x).val+(boundaryFullPowerDegree66Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree66Norm x).property (boundaryFullPowerDegree66Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree66Norm,boundaryFullPowerDegree66Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))))))=(boundaryFullPowerDegree66Block27Norm x).val+(boundaryFullPowerDegree66Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block27Norm x).property (boundaryFullPowerDegree66Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block27Norm,boundaryFullPowerDegree66Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x))))))))=(boundaryFullPowerDegree66Block25Norm x).val+(boundaryFullPowerDegree66Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block25Norm x).property (boundaryFullPowerDegree66Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block25Norm,boundaryFullPowerDegree66Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x))=c} := by

  have he : ((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x))=(boundaryImPowerRow77_12Degree66Norm x).val+(boundaryImPowerRow77_13Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree66Norm x).property (boundaryImPowerRow77_13Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree66Norm,boundaryImPowerRow77_13Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x))))=(boundaryImPowerRow77_11Degree66Norm x).val+(boundaryFullPowerDegree66Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree66Norm x).property (boundaryFullPowerDegree66Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree66Norm,boundaryFullPowerDegree66Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x))=c} := by

  have he : ((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x))=(boundaryImPowerRow77_15Degree66Norm x).val+(boundaryImPowerRow77_16Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree66Norm x).property (boundaryImPowerRow77_16Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree66Norm,boundaryImPowerRow77_16Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x))))=(boundaryImPowerRow77_14Degree66Norm x).val+(boundaryFullPowerDegree66Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree66Norm x).property (boundaryFullPowerDegree66Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree66Norm,boundaryFullPowerDegree66Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x))))))=(boundaryFullPowerDegree66Block33Norm x).val+(boundaryFullPowerDegree66Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block33Norm x).property (boundaryFullPowerDegree66Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block33Norm,boundaryFullPowerDegree66Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x))=c} := by

  have he : ((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x))=(boundaryImPowerRow77_18Degree66Norm x).val+(boundaryImPowerRow77_19Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree66Norm x).property (boundaryImPowerRow77_19Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree66Norm,boundaryImPowerRow77_19Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x))))=(boundaryImPowerRow77_17Degree66Norm x).val+(boundaryFullPowerDegree66Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree66Norm x).property (boundaryFullPowerDegree66Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree66Norm,boundaryFullPowerDegree66Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))=c} := by

  have he : ((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))=(boundaryImPowerRow77_21Degree66Norm x).val+(boundaryLowPowerRow77Degree66Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree66Norm x).property (boundaryLowPowerRow77Degree66Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree66Norm,boundaryLowPowerRow77Degree66Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))=(boundaryImPowerRow77_20Degree66Norm x).val+(boundaryFullPowerDegree66Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree66Norm x).property (boundaryFullPowerDegree66Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree66Norm,boundaryFullPowerDegree66Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))=(boundaryFullPowerDegree66Block38Norm x).val+(boundaryFullPowerDegree66Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block38Norm x).property (boundaryFullPowerDegree66Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block38Norm,boundaryFullPowerDegree66Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))))=(boundaryFullPowerDegree66Block36Norm x).val+(boundaryFullPowerDegree66Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block36Norm x).property (boundaryFullPowerDegree66Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block36Norm,boundaryFullPowerDegree66Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x)))))))))+(((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x)))))))))+(((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))))))=(boundaryFullPowerDegree66Block31Norm x).val+(boundaryFullPowerDegree66Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block31Norm x).property (boundaryFullPowerDegree66Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block31Norm,boundaryFullPowerDegree66Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree66Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x)))))))))+(((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x)))))))))))+(((((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x)))))))))+(((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x)))))))))+(((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x)))))))))))+(((((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x)))))))))+(((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x))))))))))))=(boundaryFullPowerDegree66Block21Norm x).val+(boundaryFullPowerDegree66Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree66Block21Norm x).property (boundaryFullPowerDegree66Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block21Norm,boundaryFullPowerDegree66Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree66Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 66 x=c} := by

  have he0 : boundaryFullPowerRow77 66 x=((((((((((boundaryRePowerRow77_0 66 x)+(boundaryRePowerRow77_1 66 x)))+(((boundaryRePowerRow77_2 66 x)+(((boundaryRePowerRow77_3 66 x)+(boundaryRePowerRow77_4 66 x)))))))+(((((boundaryRePowerRow77_5 66 x)+(((boundaryRePowerRow77_6 66 x)+(boundaryRePowerRow77_7 66 x)))))+(((boundaryRePowerRow77_8 66 x)+(((boundaryRePowerRow77_9 66 x)+(boundaryRePowerRow77_10 66 x)))))))))+(((((((boundaryRePowerRow77_11 66 x)+(((boundaryRePowerRow77_12 66 x)+(boundaryRePowerRow77_13 66 x)))))+(((boundaryRePowerRow77_14 66 x)+(((boundaryRePowerRow77_15 66 x)+(boundaryRePowerRow77_16 66 x)))))))+(((((boundaryRePowerRow77_17 66 x)+(((boundaryRePowerRow77_18 66 x)+(boundaryRePowerRow77_19 66 x)))))+(((boundaryRePowerRow77_20 66 x)+(((boundaryRePowerRow77_21 66 x)+(boundaryRePowerRow77_22 66 x)))))))))))+(((((((((boundaryImPowerRow77_0 66 x)+(boundaryImPowerRow77_1 66 x)))+(((boundaryImPowerRow77_2 66 x)+(((boundaryImPowerRow77_3 66 x)+(boundaryImPowerRow77_4 66 x)))))))+(((((boundaryImPowerRow77_5 66 x)+(((boundaryImPowerRow77_6 66 x)+(boundaryImPowerRow77_7 66 x)))))+(((boundaryImPowerRow77_8 66 x)+(((boundaryImPowerRow77_9 66 x)+(boundaryImPowerRow77_10 66 x)))))))))+(((((((boundaryImPowerRow77_11 66 x)+(((boundaryImPowerRow77_12 66 x)+(boundaryImPowerRow77_13 66 x)))))+(((boundaryImPowerRow77_14 66 x)+(((boundaryImPowerRow77_15 66 x)+(boundaryImPowerRow77_16 66 x)))))))+(((((boundaryImPowerRow77_17 66 x)+(((boundaryImPowerRow77_18 66 x)+(boundaryImPowerRow77_19 66 x)))))+(((boundaryImPowerRow77_20 66 x)+(((boundaryImPowerRow77_21 66 x)+(boundaryLowPowerRow77 66 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree66Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree66Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
