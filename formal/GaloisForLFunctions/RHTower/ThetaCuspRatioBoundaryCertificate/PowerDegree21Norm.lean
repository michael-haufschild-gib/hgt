import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree21Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree21Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x))=c} := by

  have he : ((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x))=(boundaryRePowerRow77_0Degree21Norm x).val+(boundaryRePowerRow77_1Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree21Norm x).property (boundaryRePowerRow77_1Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree21Norm,boundaryRePowerRow77_1Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x))=c} := by

  have he : ((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x))=(boundaryRePowerRow77_3Degree21Norm x).val+(boundaryRePowerRow77_4Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree21Norm x).property (boundaryRePowerRow77_4Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree21Norm,boundaryRePowerRow77_4Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x))))=(boundaryRePowerRow77_2Degree21Norm x).val+(boundaryFullPowerDegree21Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree21Norm x).property (boundaryFullPowerDegree21Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree21Norm,boundaryFullPowerDegree21Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x))))))=(boundaryFullPowerDegree21Block0Norm x).val+(boundaryFullPowerDegree21Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block0Norm x).property (boundaryFullPowerDegree21Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block0Norm,boundaryFullPowerDegree21Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x))=c} := by

  have he : ((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x))=(boundaryRePowerRow77_6Degree21Norm x).val+(boundaryRePowerRow77_7Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree21Norm x).property (boundaryRePowerRow77_7Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree21Norm,boundaryRePowerRow77_7Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x))))=(boundaryRePowerRow77_5Degree21Norm x).val+(boundaryFullPowerDegree21Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree21Norm x).property (boundaryFullPowerDegree21Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree21Norm,boundaryFullPowerDegree21Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))=c} := by

  have he : ((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))=(boundaryRePowerRow77_9Degree21Norm x).val+(boundaryRePowerRow77_10Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree21Norm x).property (boundaryRePowerRow77_10Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree21Norm,boundaryRePowerRow77_10Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))))=(boundaryRePowerRow77_8Degree21Norm x).val+(boundaryFullPowerDegree21Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree21Norm x).property (boundaryFullPowerDegree21Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree21Norm,boundaryFullPowerDegree21Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))))))=(boundaryFullPowerDegree21Block5Norm x).val+(boundaryFullPowerDegree21Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block5Norm x).property (boundaryFullPowerDegree21Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block5Norm,boundaryFullPowerDegree21Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x))))))))=(boundaryFullPowerDegree21Block3Norm x).val+(boundaryFullPowerDegree21Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block3Norm x).property (boundaryFullPowerDegree21Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block3Norm,boundaryFullPowerDegree21Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x))=c} := by

  have he : ((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x))=(boundaryRePowerRow77_12Degree21Norm x).val+(boundaryRePowerRow77_13Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree21Norm x).property (boundaryRePowerRow77_13Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree21Norm,boundaryRePowerRow77_13Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x))))=(boundaryRePowerRow77_11Degree21Norm x).val+(boundaryFullPowerDegree21Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree21Norm x).property (boundaryFullPowerDegree21Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree21Norm,boundaryFullPowerDegree21Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x))=c} := by

  have he : ((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x))=(boundaryRePowerRow77_15Degree21Norm x).val+(boundaryRePowerRow77_16Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree21Norm x).property (boundaryRePowerRow77_16Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree21Norm,boundaryRePowerRow77_16Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x))))=(boundaryRePowerRow77_14Degree21Norm x).val+(boundaryFullPowerDegree21Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree21Norm x).property (boundaryFullPowerDegree21Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree21Norm,boundaryFullPowerDegree21Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x))))))=(boundaryFullPowerDegree21Block11Norm x).val+(boundaryFullPowerDegree21Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block11Norm x).property (boundaryFullPowerDegree21Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block11Norm,boundaryFullPowerDegree21Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x))=c} := by

  have he : ((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x))=(boundaryRePowerRow77_18Degree21Norm x).val+(boundaryRePowerRow77_19Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree21Norm x).property (boundaryRePowerRow77_19Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree21Norm,boundaryRePowerRow77_19Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x))))=(boundaryRePowerRow77_17Degree21Norm x).val+(boundaryFullPowerDegree21Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree21Norm x).property (boundaryFullPowerDegree21Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree21Norm,boundaryFullPowerDegree21Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))=c} := by

  have he : ((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))=(boundaryRePowerRow77_21Degree21Norm x).val+(boundaryRePowerRow77_22Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree21Norm x).property (boundaryRePowerRow77_22Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree21Norm,boundaryRePowerRow77_22Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))=(boundaryRePowerRow77_20Degree21Norm x).val+(boundaryFullPowerDegree21Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree21Norm x).property (boundaryFullPowerDegree21Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree21Norm,boundaryFullPowerDegree21Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))))=(boundaryFullPowerDegree21Block16Norm x).val+(boundaryFullPowerDegree21Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block16Norm x).property (boundaryFullPowerDegree21Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block16Norm,boundaryFullPowerDegree21Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))))))=(boundaryFullPowerDegree21Block14Norm x).val+(boundaryFullPowerDegree21Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block14Norm x).property (boundaryFullPowerDegree21Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block14Norm,boundaryFullPowerDegree21Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x)))))))))+(((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x)))))))))+(((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x))))))))))=(boundaryFullPowerDegree21Block9Norm x).val+(boundaryFullPowerDegree21Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block9Norm x).property (boundaryFullPowerDegree21Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block9Norm,boundaryFullPowerDegree21Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x))=c} := by

  have he : ((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x))=(boundaryImPowerRow77_0Degree21Norm x).val+(boundaryImPowerRow77_1Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree21Norm x).property (boundaryImPowerRow77_1Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree21Norm,boundaryImPowerRow77_1Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x))=c} := by

  have he : ((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x))=(boundaryImPowerRow77_3Degree21Norm x).val+(boundaryImPowerRow77_4Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree21Norm x).property (boundaryImPowerRow77_4Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree21Norm,boundaryImPowerRow77_4Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x))))=(boundaryImPowerRow77_2Degree21Norm x).val+(boundaryFullPowerDegree21Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree21Norm x).property (boundaryFullPowerDegree21Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree21Norm,boundaryFullPowerDegree21Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x))))))=(boundaryFullPowerDegree21Block22Norm x).val+(boundaryFullPowerDegree21Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block22Norm x).property (boundaryFullPowerDegree21Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block22Norm,boundaryFullPowerDegree21Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x))=c} := by

  have he : ((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x))=(boundaryImPowerRow77_6Degree21Norm x).val+(boundaryImPowerRow77_7Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree21Norm x).property (boundaryImPowerRow77_7Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree21Norm,boundaryImPowerRow77_7Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x))))=(boundaryImPowerRow77_5Degree21Norm x).val+(boundaryFullPowerDegree21Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree21Norm x).property (boundaryFullPowerDegree21Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree21Norm,boundaryFullPowerDegree21Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))=c} := by

  have he : ((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))=(boundaryImPowerRow77_9Degree21Norm x).val+(boundaryImPowerRow77_10Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree21Norm x).property (boundaryImPowerRow77_10Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree21Norm,boundaryImPowerRow77_10Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))))=(boundaryImPowerRow77_8Degree21Norm x).val+(boundaryFullPowerDegree21Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree21Norm x).property (boundaryFullPowerDegree21Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree21Norm,boundaryFullPowerDegree21Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))))))=(boundaryFullPowerDegree21Block27Norm x).val+(boundaryFullPowerDegree21Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block27Norm x).property (boundaryFullPowerDegree21Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block27Norm,boundaryFullPowerDegree21Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x))))))))=(boundaryFullPowerDegree21Block25Norm x).val+(boundaryFullPowerDegree21Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block25Norm x).property (boundaryFullPowerDegree21Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block25Norm,boundaryFullPowerDegree21Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x))=c} := by

  have he : ((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x))=(boundaryImPowerRow77_12Degree21Norm x).val+(boundaryImPowerRow77_13Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree21Norm x).property (boundaryImPowerRow77_13Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree21Norm,boundaryImPowerRow77_13Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x))))=(boundaryImPowerRow77_11Degree21Norm x).val+(boundaryFullPowerDegree21Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree21Norm x).property (boundaryFullPowerDegree21Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree21Norm,boundaryFullPowerDegree21Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x))=c} := by

  have he : ((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x))=(boundaryImPowerRow77_15Degree21Norm x).val+(boundaryImPowerRow77_16Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree21Norm x).property (boundaryImPowerRow77_16Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree21Norm,boundaryImPowerRow77_16Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x))))=(boundaryImPowerRow77_14Degree21Norm x).val+(boundaryFullPowerDegree21Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree21Norm x).property (boundaryFullPowerDegree21Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree21Norm,boundaryFullPowerDegree21Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x))))))=(boundaryFullPowerDegree21Block33Norm x).val+(boundaryFullPowerDegree21Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block33Norm x).property (boundaryFullPowerDegree21Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block33Norm,boundaryFullPowerDegree21Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x))=c} := by

  have he : ((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x))=(boundaryImPowerRow77_18Degree21Norm x).val+(boundaryImPowerRow77_19Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree21Norm x).property (boundaryImPowerRow77_19Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree21Norm,boundaryImPowerRow77_19Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x))))=(boundaryImPowerRow77_17Degree21Norm x).val+(boundaryFullPowerDegree21Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree21Norm x).property (boundaryFullPowerDegree21Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree21Norm,boundaryFullPowerDegree21Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))=c} := by

  have he : ((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))=(boundaryImPowerRow77_21Degree21Norm x).val+(boundaryLowPowerRow77Degree21Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree21Norm x).property (boundaryLowPowerRow77Degree21Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree21Norm,boundaryLowPowerRow77Degree21Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))=(boundaryImPowerRow77_20Degree21Norm x).val+(boundaryFullPowerDegree21Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree21Norm x).property (boundaryFullPowerDegree21Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree21Norm,boundaryFullPowerDegree21Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))=(boundaryFullPowerDegree21Block38Norm x).val+(boundaryFullPowerDegree21Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block38Norm x).property (boundaryFullPowerDegree21Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block38Norm,boundaryFullPowerDegree21Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))))=(boundaryFullPowerDegree21Block36Norm x).val+(boundaryFullPowerDegree21Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block36Norm x).property (boundaryFullPowerDegree21Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block36Norm,boundaryFullPowerDegree21Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x)))))))))+(((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x)))))))))+(((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))))))=(boundaryFullPowerDegree21Block31Norm x).val+(boundaryFullPowerDegree21Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block31Norm x).property (boundaryFullPowerDegree21Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block31Norm,boundaryFullPowerDegree21Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree21Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x)))))))))+(((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x)))))))))))+(((((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x)))))))))+(((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x)))))))))+(((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x)))))))))))+(((((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x)))))))))+(((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x))))))))))))=(boundaryFullPowerDegree21Block21Norm x).val+(boundaryFullPowerDegree21Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree21Block21Norm x).property (boundaryFullPowerDegree21Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block21Norm,boundaryFullPowerDegree21Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree21Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 21 x=c} := by

  have he0 : boundaryFullPowerRow77 21 x=((((((((((boundaryRePowerRow77_0 21 x)+(boundaryRePowerRow77_1 21 x)))+(((boundaryRePowerRow77_2 21 x)+(((boundaryRePowerRow77_3 21 x)+(boundaryRePowerRow77_4 21 x)))))))+(((((boundaryRePowerRow77_5 21 x)+(((boundaryRePowerRow77_6 21 x)+(boundaryRePowerRow77_7 21 x)))))+(((boundaryRePowerRow77_8 21 x)+(((boundaryRePowerRow77_9 21 x)+(boundaryRePowerRow77_10 21 x)))))))))+(((((((boundaryRePowerRow77_11 21 x)+(((boundaryRePowerRow77_12 21 x)+(boundaryRePowerRow77_13 21 x)))))+(((boundaryRePowerRow77_14 21 x)+(((boundaryRePowerRow77_15 21 x)+(boundaryRePowerRow77_16 21 x)))))))+(((((boundaryRePowerRow77_17 21 x)+(((boundaryRePowerRow77_18 21 x)+(boundaryRePowerRow77_19 21 x)))))+(((boundaryRePowerRow77_20 21 x)+(((boundaryRePowerRow77_21 21 x)+(boundaryRePowerRow77_22 21 x)))))))))))+(((((((((boundaryImPowerRow77_0 21 x)+(boundaryImPowerRow77_1 21 x)))+(((boundaryImPowerRow77_2 21 x)+(((boundaryImPowerRow77_3 21 x)+(boundaryImPowerRow77_4 21 x)))))))+(((((boundaryImPowerRow77_5 21 x)+(((boundaryImPowerRow77_6 21 x)+(boundaryImPowerRow77_7 21 x)))))+(((boundaryImPowerRow77_8 21 x)+(((boundaryImPowerRow77_9 21 x)+(boundaryImPowerRow77_10 21 x)))))))))+(((((((boundaryImPowerRow77_11 21 x)+(((boundaryImPowerRow77_12 21 x)+(boundaryImPowerRow77_13 21 x)))))+(((boundaryImPowerRow77_14 21 x)+(((boundaryImPowerRow77_15 21 x)+(boundaryImPowerRow77_16 21 x)))))))+(((((boundaryImPowerRow77_17 21 x)+(((boundaryImPowerRow77_18 21 x)+(boundaryImPowerRow77_19 21 x)))))+(((boundaryImPowerRow77_20 21 x)+(((boundaryImPowerRow77_21 21 x)+(boundaryLowPowerRow77 21 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree21Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree21Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
