import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree24Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree24Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x))=c} := by

  have he : ((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x))=(boundaryRePowerRow77_0Degree24Norm x).val+(boundaryRePowerRow77_1Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree24Norm x).property (boundaryRePowerRow77_1Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree24Norm,boundaryRePowerRow77_1Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x))=c} := by

  have he : ((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x))=(boundaryRePowerRow77_3Degree24Norm x).val+(boundaryRePowerRow77_4Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree24Norm x).property (boundaryRePowerRow77_4Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree24Norm,boundaryRePowerRow77_4Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x))))=(boundaryRePowerRow77_2Degree24Norm x).val+(boundaryFullPowerDegree24Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree24Norm x).property (boundaryFullPowerDegree24Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree24Norm,boundaryFullPowerDegree24Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x))))))=(boundaryFullPowerDegree24Block0Norm x).val+(boundaryFullPowerDegree24Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block0Norm x).property (boundaryFullPowerDegree24Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block0Norm,boundaryFullPowerDegree24Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x))=c} := by

  have he : ((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x))=(boundaryRePowerRow77_6Degree24Norm x).val+(boundaryRePowerRow77_7Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree24Norm x).property (boundaryRePowerRow77_7Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree24Norm,boundaryRePowerRow77_7Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x))))=(boundaryRePowerRow77_5Degree24Norm x).val+(boundaryFullPowerDegree24Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree24Norm x).property (boundaryFullPowerDegree24Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree24Norm,boundaryFullPowerDegree24Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))=c} := by

  have he : ((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))=(boundaryRePowerRow77_9Degree24Norm x).val+(boundaryRePowerRow77_10Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree24Norm x).property (boundaryRePowerRow77_10Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree24Norm,boundaryRePowerRow77_10Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))))=(boundaryRePowerRow77_8Degree24Norm x).val+(boundaryFullPowerDegree24Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree24Norm x).property (boundaryFullPowerDegree24Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree24Norm,boundaryFullPowerDegree24Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))))))=(boundaryFullPowerDegree24Block5Norm x).val+(boundaryFullPowerDegree24Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block5Norm x).property (boundaryFullPowerDegree24Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block5Norm,boundaryFullPowerDegree24Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x))))))))=(boundaryFullPowerDegree24Block3Norm x).val+(boundaryFullPowerDegree24Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block3Norm x).property (boundaryFullPowerDegree24Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block3Norm,boundaryFullPowerDegree24Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x))=c} := by

  have he : ((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x))=(boundaryRePowerRow77_12Degree24Norm x).val+(boundaryRePowerRow77_13Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree24Norm x).property (boundaryRePowerRow77_13Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree24Norm,boundaryRePowerRow77_13Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x))))=(boundaryRePowerRow77_11Degree24Norm x).val+(boundaryFullPowerDegree24Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree24Norm x).property (boundaryFullPowerDegree24Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree24Norm,boundaryFullPowerDegree24Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x))=c} := by

  have he : ((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x))=(boundaryRePowerRow77_15Degree24Norm x).val+(boundaryRePowerRow77_16Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree24Norm x).property (boundaryRePowerRow77_16Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree24Norm,boundaryRePowerRow77_16Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x))))=(boundaryRePowerRow77_14Degree24Norm x).val+(boundaryFullPowerDegree24Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree24Norm x).property (boundaryFullPowerDegree24Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree24Norm,boundaryFullPowerDegree24Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x))))))=(boundaryFullPowerDegree24Block11Norm x).val+(boundaryFullPowerDegree24Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block11Norm x).property (boundaryFullPowerDegree24Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block11Norm,boundaryFullPowerDegree24Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x))=c} := by

  have he : ((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x))=(boundaryRePowerRow77_18Degree24Norm x).val+(boundaryRePowerRow77_19Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree24Norm x).property (boundaryRePowerRow77_19Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree24Norm,boundaryRePowerRow77_19Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x))))=(boundaryRePowerRow77_17Degree24Norm x).val+(boundaryFullPowerDegree24Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree24Norm x).property (boundaryFullPowerDegree24Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree24Norm,boundaryFullPowerDegree24Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))=c} := by

  have he : ((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))=(boundaryRePowerRow77_21Degree24Norm x).val+(boundaryRePowerRow77_22Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree24Norm x).property (boundaryRePowerRow77_22Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree24Norm,boundaryRePowerRow77_22Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))=(boundaryRePowerRow77_20Degree24Norm x).val+(boundaryFullPowerDegree24Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree24Norm x).property (boundaryFullPowerDegree24Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree24Norm,boundaryFullPowerDegree24Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))))=(boundaryFullPowerDegree24Block16Norm x).val+(boundaryFullPowerDegree24Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block16Norm x).property (boundaryFullPowerDegree24Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block16Norm,boundaryFullPowerDegree24Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))))))=(boundaryFullPowerDegree24Block14Norm x).val+(boundaryFullPowerDegree24Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block14Norm x).property (boundaryFullPowerDegree24Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block14Norm,boundaryFullPowerDegree24Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x)))))))))+(((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x)))))))))+(((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x))))))))))=(boundaryFullPowerDegree24Block9Norm x).val+(boundaryFullPowerDegree24Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block9Norm x).property (boundaryFullPowerDegree24Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block9Norm,boundaryFullPowerDegree24Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x))=c} := by

  have he : ((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x))=(boundaryImPowerRow77_0Degree24Norm x).val+(boundaryImPowerRow77_1Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree24Norm x).property (boundaryImPowerRow77_1Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree24Norm,boundaryImPowerRow77_1Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x))=c} := by

  have he : ((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x))=(boundaryImPowerRow77_3Degree24Norm x).val+(boundaryImPowerRow77_4Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree24Norm x).property (boundaryImPowerRow77_4Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree24Norm,boundaryImPowerRow77_4Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x))))=(boundaryImPowerRow77_2Degree24Norm x).val+(boundaryFullPowerDegree24Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree24Norm x).property (boundaryFullPowerDegree24Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree24Norm,boundaryFullPowerDegree24Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x))))))=(boundaryFullPowerDegree24Block22Norm x).val+(boundaryFullPowerDegree24Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block22Norm x).property (boundaryFullPowerDegree24Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block22Norm,boundaryFullPowerDegree24Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x))=c} := by

  have he : ((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x))=(boundaryImPowerRow77_6Degree24Norm x).val+(boundaryImPowerRow77_7Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree24Norm x).property (boundaryImPowerRow77_7Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree24Norm,boundaryImPowerRow77_7Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x))))=(boundaryImPowerRow77_5Degree24Norm x).val+(boundaryFullPowerDegree24Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree24Norm x).property (boundaryFullPowerDegree24Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree24Norm,boundaryFullPowerDegree24Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))=c} := by

  have he : ((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))=(boundaryImPowerRow77_9Degree24Norm x).val+(boundaryImPowerRow77_10Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree24Norm x).property (boundaryImPowerRow77_10Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree24Norm,boundaryImPowerRow77_10Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))))=(boundaryImPowerRow77_8Degree24Norm x).val+(boundaryFullPowerDegree24Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree24Norm x).property (boundaryFullPowerDegree24Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree24Norm,boundaryFullPowerDegree24Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))))))=(boundaryFullPowerDegree24Block27Norm x).val+(boundaryFullPowerDegree24Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block27Norm x).property (boundaryFullPowerDegree24Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block27Norm,boundaryFullPowerDegree24Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x))))))))=(boundaryFullPowerDegree24Block25Norm x).val+(boundaryFullPowerDegree24Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block25Norm x).property (boundaryFullPowerDegree24Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block25Norm,boundaryFullPowerDegree24Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x))=c} := by

  have he : ((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x))=(boundaryImPowerRow77_12Degree24Norm x).val+(boundaryImPowerRow77_13Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree24Norm x).property (boundaryImPowerRow77_13Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree24Norm,boundaryImPowerRow77_13Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x))))=(boundaryImPowerRow77_11Degree24Norm x).val+(boundaryFullPowerDegree24Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree24Norm x).property (boundaryFullPowerDegree24Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree24Norm,boundaryFullPowerDegree24Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x))=c} := by

  have he : ((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x))=(boundaryImPowerRow77_15Degree24Norm x).val+(boundaryImPowerRow77_16Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree24Norm x).property (boundaryImPowerRow77_16Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree24Norm,boundaryImPowerRow77_16Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x))))=(boundaryImPowerRow77_14Degree24Norm x).val+(boundaryFullPowerDegree24Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree24Norm x).property (boundaryFullPowerDegree24Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree24Norm,boundaryFullPowerDegree24Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x))))))=(boundaryFullPowerDegree24Block33Norm x).val+(boundaryFullPowerDegree24Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block33Norm x).property (boundaryFullPowerDegree24Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block33Norm,boundaryFullPowerDegree24Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x))=c} := by

  have he : ((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x))=(boundaryImPowerRow77_18Degree24Norm x).val+(boundaryImPowerRow77_19Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree24Norm x).property (boundaryImPowerRow77_19Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree24Norm,boundaryImPowerRow77_19Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x))))=(boundaryImPowerRow77_17Degree24Norm x).val+(boundaryFullPowerDegree24Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree24Norm x).property (boundaryFullPowerDegree24Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree24Norm,boundaryFullPowerDegree24Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))=c} := by

  have he : ((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))=(boundaryImPowerRow77_21Degree24Norm x).val+(boundaryLowPowerRow77Degree24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree24Norm x).property (boundaryLowPowerRow77Degree24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree24Norm,boundaryLowPowerRow77Degree24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))=(boundaryImPowerRow77_20Degree24Norm x).val+(boundaryFullPowerDegree24Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree24Norm x).property (boundaryFullPowerDegree24Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree24Norm,boundaryFullPowerDegree24Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))=(boundaryFullPowerDegree24Block38Norm x).val+(boundaryFullPowerDegree24Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block38Norm x).property (boundaryFullPowerDegree24Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block38Norm,boundaryFullPowerDegree24Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))))=(boundaryFullPowerDegree24Block36Norm x).val+(boundaryFullPowerDegree24Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block36Norm x).property (boundaryFullPowerDegree24Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block36Norm,boundaryFullPowerDegree24Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x)))))))))+(((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x)))))))))+(((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))))))=(boundaryFullPowerDegree24Block31Norm x).val+(boundaryFullPowerDegree24Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block31Norm x).property (boundaryFullPowerDegree24Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block31Norm,boundaryFullPowerDegree24Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree24Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x)))))))))+(((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x)))))))))))+(((((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x)))))))))+(((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x)))))))))+(((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x)))))))))))+(((((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x)))))))))+(((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x))))))))))))=(boundaryFullPowerDegree24Block21Norm x).val+(boundaryFullPowerDegree24Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree24Block21Norm x).property (boundaryFullPowerDegree24Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block21Norm,boundaryFullPowerDegree24Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree24Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 24 x=c} := by

  have he0 : boundaryFullPowerRow77 24 x=((((((((((boundaryRePowerRow77_0 24 x)+(boundaryRePowerRow77_1 24 x)))+(((boundaryRePowerRow77_2 24 x)+(((boundaryRePowerRow77_3 24 x)+(boundaryRePowerRow77_4 24 x)))))))+(((((boundaryRePowerRow77_5 24 x)+(((boundaryRePowerRow77_6 24 x)+(boundaryRePowerRow77_7 24 x)))))+(((boundaryRePowerRow77_8 24 x)+(((boundaryRePowerRow77_9 24 x)+(boundaryRePowerRow77_10 24 x)))))))))+(((((((boundaryRePowerRow77_11 24 x)+(((boundaryRePowerRow77_12 24 x)+(boundaryRePowerRow77_13 24 x)))))+(((boundaryRePowerRow77_14 24 x)+(((boundaryRePowerRow77_15 24 x)+(boundaryRePowerRow77_16 24 x)))))))+(((((boundaryRePowerRow77_17 24 x)+(((boundaryRePowerRow77_18 24 x)+(boundaryRePowerRow77_19 24 x)))))+(((boundaryRePowerRow77_20 24 x)+(((boundaryRePowerRow77_21 24 x)+(boundaryRePowerRow77_22 24 x)))))))))))+(((((((((boundaryImPowerRow77_0 24 x)+(boundaryImPowerRow77_1 24 x)))+(((boundaryImPowerRow77_2 24 x)+(((boundaryImPowerRow77_3 24 x)+(boundaryImPowerRow77_4 24 x)))))))+(((((boundaryImPowerRow77_5 24 x)+(((boundaryImPowerRow77_6 24 x)+(boundaryImPowerRow77_7 24 x)))))+(((boundaryImPowerRow77_8 24 x)+(((boundaryImPowerRow77_9 24 x)+(boundaryImPowerRow77_10 24 x)))))))))+(((((((boundaryImPowerRow77_11 24 x)+(((boundaryImPowerRow77_12 24 x)+(boundaryImPowerRow77_13 24 x)))))+(((boundaryImPowerRow77_14 24 x)+(((boundaryImPowerRow77_15 24 x)+(boundaryImPowerRow77_16 24 x)))))))+(((((boundaryImPowerRow77_17 24 x)+(((boundaryImPowerRow77_18 24 x)+(boundaryImPowerRow77_19 24 x)))))+(((boundaryImPowerRow77_20 24 x)+(((boundaryImPowerRow77_21 24 x)+(boundaryLowPowerRow77 24 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree24Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree24Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
