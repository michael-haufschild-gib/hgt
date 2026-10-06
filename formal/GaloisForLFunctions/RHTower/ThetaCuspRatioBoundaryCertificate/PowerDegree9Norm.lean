import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree9Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree9Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x))=c} := by

  have he : ((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x))=(boundaryRePowerRow77_0Degree9Norm x).val+(boundaryRePowerRow77_1Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree9Norm x).property (boundaryRePowerRow77_1Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree9Norm,boundaryRePowerRow77_1Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x))=c} := by

  have he : ((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x))=(boundaryRePowerRow77_3Degree9Norm x).val+(boundaryRePowerRow77_4Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree9Norm x).property (boundaryRePowerRow77_4Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree9Norm,boundaryRePowerRow77_4Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x))))=(boundaryRePowerRow77_2Degree9Norm x).val+(boundaryFullPowerDegree9Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree9Norm x).property (boundaryFullPowerDegree9Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree9Norm,boundaryFullPowerDegree9Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x))))))=(boundaryFullPowerDegree9Block0Norm x).val+(boundaryFullPowerDegree9Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block0Norm x).property (boundaryFullPowerDegree9Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block0Norm,boundaryFullPowerDegree9Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x))=c} := by

  have he : ((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x))=(boundaryRePowerRow77_6Degree9Norm x).val+(boundaryRePowerRow77_7Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree9Norm x).property (boundaryRePowerRow77_7Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree9Norm,boundaryRePowerRow77_7Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x))))=(boundaryRePowerRow77_5Degree9Norm x).val+(boundaryFullPowerDegree9Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree9Norm x).property (boundaryFullPowerDegree9Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree9Norm,boundaryFullPowerDegree9Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))=c} := by

  have he : ((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))=(boundaryRePowerRow77_9Degree9Norm x).val+(boundaryRePowerRow77_10Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree9Norm x).property (boundaryRePowerRow77_10Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree9Norm,boundaryRePowerRow77_10Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))))=(boundaryRePowerRow77_8Degree9Norm x).val+(boundaryFullPowerDegree9Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree9Norm x).property (boundaryFullPowerDegree9Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree9Norm,boundaryFullPowerDegree9Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))))))=(boundaryFullPowerDegree9Block5Norm x).val+(boundaryFullPowerDegree9Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block5Norm x).property (boundaryFullPowerDegree9Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block5Norm,boundaryFullPowerDegree9Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x))))))))=(boundaryFullPowerDegree9Block3Norm x).val+(boundaryFullPowerDegree9Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block3Norm x).property (boundaryFullPowerDegree9Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block3Norm,boundaryFullPowerDegree9Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x))=c} := by

  have he : ((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x))=(boundaryRePowerRow77_12Degree9Norm x).val+(boundaryRePowerRow77_13Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree9Norm x).property (boundaryRePowerRow77_13Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree9Norm,boundaryRePowerRow77_13Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x))))=(boundaryRePowerRow77_11Degree9Norm x).val+(boundaryFullPowerDegree9Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree9Norm x).property (boundaryFullPowerDegree9Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree9Norm,boundaryFullPowerDegree9Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x))=c} := by

  have he : ((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x))=(boundaryRePowerRow77_15Degree9Norm x).val+(boundaryRePowerRow77_16Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree9Norm x).property (boundaryRePowerRow77_16Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree9Norm,boundaryRePowerRow77_16Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x))))=(boundaryRePowerRow77_14Degree9Norm x).val+(boundaryFullPowerDegree9Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree9Norm x).property (boundaryFullPowerDegree9Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree9Norm,boundaryFullPowerDegree9Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x))))))=(boundaryFullPowerDegree9Block11Norm x).val+(boundaryFullPowerDegree9Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block11Norm x).property (boundaryFullPowerDegree9Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block11Norm,boundaryFullPowerDegree9Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x))=c} := by

  have he : ((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x))=(boundaryRePowerRow77_18Degree9Norm x).val+(boundaryRePowerRow77_19Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree9Norm x).property (boundaryRePowerRow77_19Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree9Norm,boundaryRePowerRow77_19Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x))))=(boundaryRePowerRow77_17Degree9Norm x).val+(boundaryFullPowerDegree9Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree9Norm x).property (boundaryFullPowerDegree9Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree9Norm,boundaryFullPowerDegree9Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))=c} := by

  have he : ((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))=(boundaryRePowerRow77_21Degree9Norm x).val+(boundaryRePowerRow77_22Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree9Norm x).property (boundaryRePowerRow77_22Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree9Norm,boundaryRePowerRow77_22Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))=(boundaryRePowerRow77_20Degree9Norm x).val+(boundaryFullPowerDegree9Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree9Norm x).property (boundaryFullPowerDegree9Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree9Norm,boundaryFullPowerDegree9Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))))=(boundaryFullPowerDegree9Block16Norm x).val+(boundaryFullPowerDegree9Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block16Norm x).property (boundaryFullPowerDegree9Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block16Norm,boundaryFullPowerDegree9Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))))))=(boundaryFullPowerDegree9Block14Norm x).val+(boundaryFullPowerDegree9Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block14Norm x).property (boundaryFullPowerDegree9Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block14Norm,boundaryFullPowerDegree9Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x)))))))))+(((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x)))))))))+(((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x))))))))))=(boundaryFullPowerDegree9Block9Norm x).val+(boundaryFullPowerDegree9Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block9Norm x).property (boundaryFullPowerDegree9Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block9Norm,boundaryFullPowerDegree9Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x))=c} := by

  have he : ((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x))=(boundaryImPowerRow77_0Degree9Norm x).val+(boundaryImPowerRow77_1Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree9Norm x).property (boundaryImPowerRow77_1Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree9Norm,boundaryImPowerRow77_1Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x))=c} := by

  have he : ((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x))=(boundaryImPowerRow77_3Degree9Norm x).val+(boundaryImPowerRow77_4Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree9Norm x).property (boundaryImPowerRow77_4Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree9Norm,boundaryImPowerRow77_4Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x))))=(boundaryImPowerRow77_2Degree9Norm x).val+(boundaryFullPowerDegree9Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree9Norm x).property (boundaryFullPowerDegree9Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree9Norm,boundaryFullPowerDegree9Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x))))))=(boundaryFullPowerDegree9Block22Norm x).val+(boundaryFullPowerDegree9Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block22Norm x).property (boundaryFullPowerDegree9Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block22Norm,boundaryFullPowerDegree9Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x))=c} := by

  have he : ((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x))=(boundaryImPowerRow77_6Degree9Norm x).val+(boundaryImPowerRow77_7Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree9Norm x).property (boundaryImPowerRow77_7Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree9Norm,boundaryImPowerRow77_7Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x))))=(boundaryImPowerRow77_5Degree9Norm x).val+(boundaryFullPowerDegree9Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree9Norm x).property (boundaryFullPowerDegree9Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree9Norm,boundaryFullPowerDegree9Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))=c} := by

  have he : ((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))=(boundaryImPowerRow77_9Degree9Norm x).val+(boundaryImPowerRow77_10Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree9Norm x).property (boundaryImPowerRow77_10Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree9Norm,boundaryImPowerRow77_10Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))))=(boundaryImPowerRow77_8Degree9Norm x).val+(boundaryFullPowerDegree9Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree9Norm x).property (boundaryFullPowerDegree9Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree9Norm,boundaryFullPowerDegree9Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))))))=(boundaryFullPowerDegree9Block27Norm x).val+(boundaryFullPowerDegree9Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block27Norm x).property (boundaryFullPowerDegree9Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block27Norm,boundaryFullPowerDegree9Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x))))))))=(boundaryFullPowerDegree9Block25Norm x).val+(boundaryFullPowerDegree9Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block25Norm x).property (boundaryFullPowerDegree9Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block25Norm,boundaryFullPowerDegree9Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x))=c} := by

  have he : ((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x))=(boundaryImPowerRow77_12Degree9Norm x).val+(boundaryImPowerRow77_13Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree9Norm x).property (boundaryImPowerRow77_13Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree9Norm,boundaryImPowerRow77_13Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x))))=(boundaryImPowerRow77_11Degree9Norm x).val+(boundaryFullPowerDegree9Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree9Norm x).property (boundaryFullPowerDegree9Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree9Norm,boundaryFullPowerDegree9Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x))=c} := by

  have he : ((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x))=(boundaryImPowerRow77_15Degree9Norm x).val+(boundaryImPowerRow77_16Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree9Norm x).property (boundaryImPowerRow77_16Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree9Norm,boundaryImPowerRow77_16Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x))))=(boundaryImPowerRow77_14Degree9Norm x).val+(boundaryFullPowerDegree9Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree9Norm x).property (boundaryFullPowerDegree9Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree9Norm,boundaryFullPowerDegree9Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x))))))=(boundaryFullPowerDegree9Block33Norm x).val+(boundaryFullPowerDegree9Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block33Norm x).property (boundaryFullPowerDegree9Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block33Norm,boundaryFullPowerDegree9Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x))=c} := by

  have he : ((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x))=(boundaryImPowerRow77_18Degree9Norm x).val+(boundaryImPowerRow77_19Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree9Norm x).property (boundaryImPowerRow77_19Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree9Norm,boundaryImPowerRow77_19Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x))))=(boundaryImPowerRow77_17Degree9Norm x).val+(boundaryFullPowerDegree9Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree9Norm x).property (boundaryFullPowerDegree9Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree9Norm,boundaryFullPowerDegree9Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))=c} := by

  have he : ((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))=(boundaryImPowerRow77_21Degree9Norm x).val+(boundaryLowPowerRow77Degree9Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree9Norm x).property (boundaryLowPowerRow77Degree9Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree9Norm,boundaryLowPowerRow77Degree9Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))=(boundaryImPowerRow77_20Degree9Norm x).val+(boundaryFullPowerDegree9Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree9Norm x).property (boundaryFullPowerDegree9Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree9Norm,boundaryFullPowerDegree9Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))=(boundaryFullPowerDegree9Block38Norm x).val+(boundaryFullPowerDegree9Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block38Norm x).property (boundaryFullPowerDegree9Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block38Norm,boundaryFullPowerDegree9Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))))=(boundaryFullPowerDegree9Block36Norm x).val+(boundaryFullPowerDegree9Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block36Norm x).property (boundaryFullPowerDegree9Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block36Norm,boundaryFullPowerDegree9Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x)))))))))+(((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x)))))))))+(((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))))))=(boundaryFullPowerDegree9Block31Norm x).val+(boundaryFullPowerDegree9Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block31Norm x).property (boundaryFullPowerDegree9Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block31Norm,boundaryFullPowerDegree9Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree9Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x)))))))))+(((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x)))))))))))+(((((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x)))))))))+(((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x)))))))))+(((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x)))))))))))+(((((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x)))))))))+(((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x))))))))))))=(boundaryFullPowerDegree9Block21Norm x).val+(boundaryFullPowerDegree9Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree9Block21Norm x).property (boundaryFullPowerDegree9Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block21Norm,boundaryFullPowerDegree9Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree9Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 9 x=c} := by

  have he0 : boundaryFullPowerRow77 9 x=((((((((((boundaryRePowerRow77_0 9 x)+(boundaryRePowerRow77_1 9 x)))+(((boundaryRePowerRow77_2 9 x)+(((boundaryRePowerRow77_3 9 x)+(boundaryRePowerRow77_4 9 x)))))))+(((((boundaryRePowerRow77_5 9 x)+(((boundaryRePowerRow77_6 9 x)+(boundaryRePowerRow77_7 9 x)))))+(((boundaryRePowerRow77_8 9 x)+(((boundaryRePowerRow77_9 9 x)+(boundaryRePowerRow77_10 9 x)))))))))+(((((((boundaryRePowerRow77_11 9 x)+(((boundaryRePowerRow77_12 9 x)+(boundaryRePowerRow77_13 9 x)))))+(((boundaryRePowerRow77_14 9 x)+(((boundaryRePowerRow77_15 9 x)+(boundaryRePowerRow77_16 9 x)))))))+(((((boundaryRePowerRow77_17 9 x)+(((boundaryRePowerRow77_18 9 x)+(boundaryRePowerRow77_19 9 x)))))+(((boundaryRePowerRow77_20 9 x)+(((boundaryRePowerRow77_21 9 x)+(boundaryRePowerRow77_22 9 x)))))))))))+(((((((((boundaryImPowerRow77_0 9 x)+(boundaryImPowerRow77_1 9 x)))+(((boundaryImPowerRow77_2 9 x)+(((boundaryImPowerRow77_3 9 x)+(boundaryImPowerRow77_4 9 x)))))))+(((((boundaryImPowerRow77_5 9 x)+(((boundaryImPowerRow77_6 9 x)+(boundaryImPowerRow77_7 9 x)))))+(((boundaryImPowerRow77_8 9 x)+(((boundaryImPowerRow77_9 9 x)+(boundaryImPowerRow77_10 9 x)))))))))+(((((((boundaryImPowerRow77_11 9 x)+(((boundaryImPowerRow77_12 9 x)+(boundaryImPowerRow77_13 9 x)))))+(((boundaryImPowerRow77_14 9 x)+(((boundaryImPowerRow77_15 9 x)+(boundaryImPowerRow77_16 9 x)))))))+(((((boundaryImPowerRow77_17 9 x)+(((boundaryImPowerRow77_18 9 x)+(boundaryImPowerRow77_19 9 x)))))+(((boundaryImPowerRow77_20 9 x)+(((boundaryImPowerRow77_21 9 x)+(boundaryLowPowerRow77 9 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree9Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree9Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
