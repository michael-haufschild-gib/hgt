import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree47Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree47Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x))=c} := by

  have he : ((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x))=(boundaryRePowerRow77_0Degree47Norm x).val+(boundaryRePowerRow77_1Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree47Norm x).property (boundaryRePowerRow77_1Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree47Norm,boundaryRePowerRow77_1Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x))=c} := by

  have he : ((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x))=(boundaryRePowerRow77_3Degree47Norm x).val+(boundaryRePowerRow77_4Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree47Norm x).property (boundaryRePowerRow77_4Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree47Norm,boundaryRePowerRow77_4Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x))))=(boundaryRePowerRow77_2Degree47Norm x).val+(boundaryFullPowerDegree47Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree47Norm x).property (boundaryFullPowerDegree47Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree47Norm,boundaryFullPowerDegree47Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x))))))=(boundaryFullPowerDegree47Block0Norm x).val+(boundaryFullPowerDegree47Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block0Norm x).property (boundaryFullPowerDegree47Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block0Norm,boundaryFullPowerDegree47Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x))=c} := by

  have he : ((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x))=(boundaryRePowerRow77_6Degree47Norm x).val+(boundaryRePowerRow77_7Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree47Norm x).property (boundaryRePowerRow77_7Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree47Norm,boundaryRePowerRow77_7Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x))))=(boundaryRePowerRow77_5Degree47Norm x).val+(boundaryFullPowerDegree47Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree47Norm x).property (boundaryFullPowerDegree47Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree47Norm,boundaryFullPowerDegree47Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))=c} := by

  have he : ((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))=(boundaryRePowerRow77_9Degree47Norm x).val+(boundaryRePowerRow77_10Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree47Norm x).property (boundaryRePowerRow77_10Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree47Norm,boundaryRePowerRow77_10Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))))=(boundaryRePowerRow77_8Degree47Norm x).val+(boundaryFullPowerDegree47Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree47Norm x).property (boundaryFullPowerDegree47Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree47Norm,boundaryFullPowerDegree47Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))))))=(boundaryFullPowerDegree47Block5Norm x).val+(boundaryFullPowerDegree47Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block5Norm x).property (boundaryFullPowerDegree47Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block5Norm,boundaryFullPowerDegree47Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x))))))))=(boundaryFullPowerDegree47Block3Norm x).val+(boundaryFullPowerDegree47Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block3Norm x).property (boundaryFullPowerDegree47Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block3Norm,boundaryFullPowerDegree47Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x))=c} := by

  have he : ((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x))=(boundaryRePowerRow77_12Degree47Norm x).val+(boundaryRePowerRow77_13Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree47Norm x).property (boundaryRePowerRow77_13Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree47Norm,boundaryRePowerRow77_13Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x))))=(boundaryRePowerRow77_11Degree47Norm x).val+(boundaryFullPowerDegree47Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree47Norm x).property (boundaryFullPowerDegree47Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree47Norm,boundaryFullPowerDegree47Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x))=c} := by

  have he : ((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x))=(boundaryRePowerRow77_15Degree47Norm x).val+(boundaryRePowerRow77_16Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree47Norm x).property (boundaryRePowerRow77_16Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree47Norm,boundaryRePowerRow77_16Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x))))=(boundaryRePowerRow77_14Degree47Norm x).val+(boundaryFullPowerDegree47Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree47Norm x).property (boundaryFullPowerDegree47Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree47Norm,boundaryFullPowerDegree47Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x))))))=(boundaryFullPowerDegree47Block11Norm x).val+(boundaryFullPowerDegree47Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block11Norm x).property (boundaryFullPowerDegree47Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block11Norm,boundaryFullPowerDegree47Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x))=c} := by

  have he : ((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x))=(boundaryRePowerRow77_18Degree47Norm x).val+(boundaryRePowerRow77_19Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree47Norm x).property (boundaryRePowerRow77_19Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree47Norm,boundaryRePowerRow77_19Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x))))=(boundaryRePowerRow77_17Degree47Norm x).val+(boundaryFullPowerDegree47Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree47Norm x).property (boundaryFullPowerDegree47Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree47Norm,boundaryFullPowerDegree47Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))=c} := by

  have he : ((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))=(boundaryRePowerRow77_21Degree47Norm x).val+(boundaryRePowerRow77_22Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree47Norm x).property (boundaryRePowerRow77_22Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree47Norm,boundaryRePowerRow77_22Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))=(boundaryRePowerRow77_20Degree47Norm x).val+(boundaryFullPowerDegree47Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree47Norm x).property (boundaryFullPowerDegree47Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree47Norm,boundaryFullPowerDegree47Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))))=(boundaryFullPowerDegree47Block16Norm x).val+(boundaryFullPowerDegree47Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block16Norm x).property (boundaryFullPowerDegree47Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block16Norm,boundaryFullPowerDegree47Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))))))=(boundaryFullPowerDegree47Block14Norm x).val+(boundaryFullPowerDegree47Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block14Norm x).property (boundaryFullPowerDegree47Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block14Norm,boundaryFullPowerDegree47Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x)))))))))+(((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x)))))))))+(((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x))))))))))=(boundaryFullPowerDegree47Block9Norm x).val+(boundaryFullPowerDegree47Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block9Norm x).property (boundaryFullPowerDegree47Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block9Norm,boundaryFullPowerDegree47Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x))=c} := by

  have he : ((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x))=(boundaryImPowerRow77_0Degree47Norm x).val+(boundaryImPowerRow77_1Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree47Norm x).property (boundaryImPowerRow77_1Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree47Norm,boundaryImPowerRow77_1Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x))=c} := by

  have he : ((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x))=(boundaryImPowerRow77_3Degree47Norm x).val+(boundaryImPowerRow77_4Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree47Norm x).property (boundaryImPowerRow77_4Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree47Norm,boundaryImPowerRow77_4Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x))))=(boundaryImPowerRow77_2Degree47Norm x).val+(boundaryFullPowerDegree47Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree47Norm x).property (boundaryFullPowerDegree47Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree47Norm,boundaryFullPowerDegree47Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x))))))=(boundaryFullPowerDegree47Block22Norm x).val+(boundaryFullPowerDegree47Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block22Norm x).property (boundaryFullPowerDegree47Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block22Norm,boundaryFullPowerDegree47Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x))=c} := by

  have he : ((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x))=(boundaryImPowerRow77_6Degree47Norm x).val+(boundaryImPowerRow77_7Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree47Norm x).property (boundaryImPowerRow77_7Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree47Norm,boundaryImPowerRow77_7Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x))))=(boundaryImPowerRow77_5Degree47Norm x).val+(boundaryFullPowerDegree47Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree47Norm x).property (boundaryFullPowerDegree47Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree47Norm,boundaryFullPowerDegree47Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))=c} := by

  have he : ((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))=(boundaryImPowerRow77_9Degree47Norm x).val+(boundaryImPowerRow77_10Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree47Norm x).property (boundaryImPowerRow77_10Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree47Norm,boundaryImPowerRow77_10Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))))=(boundaryImPowerRow77_8Degree47Norm x).val+(boundaryFullPowerDegree47Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree47Norm x).property (boundaryFullPowerDegree47Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree47Norm,boundaryFullPowerDegree47Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))))))=(boundaryFullPowerDegree47Block27Norm x).val+(boundaryFullPowerDegree47Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block27Norm x).property (boundaryFullPowerDegree47Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block27Norm,boundaryFullPowerDegree47Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x))))))))=(boundaryFullPowerDegree47Block25Norm x).val+(boundaryFullPowerDegree47Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block25Norm x).property (boundaryFullPowerDegree47Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block25Norm,boundaryFullPowerDegree47Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x))=c} := by

  have he : ((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x))=(boundaryImPowerRow77_12Degree47Norm x).val+(boundaryImPowerRow77_13Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree47Norm x).property (boundaryImPowerRow77_13Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree47Norm,boundaryImPowerRow77_13Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x))))=(boundaryImPowerRow77_11Degree47Norm x).val+(boundaryFullPowerDegree47Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree47Norm x).property (boundaryFullPowerDegree47Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree47Norm,boundaryFullPowerDegree47Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x))=c} := by

  have he : ((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x))=(boundaryImPowerRow77_15Degree47Norm x).val+(boundaryImPowerRow77_16Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree47Norm x).property (boundaryImPowerRow77_16Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree47Norm,boundaryImPowerRow77_16Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x))))=(boundaryImPowerRow77_14Degree47Norm x).val+(boundaryFullPowerDegree47Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree47Norm x).property (boundaryFullPowerDegree47Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree47Norm,boundaryFullPowerDegree47Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x))))))=(boundaryFullPowerDegree47Block33Norm x).val+(boundaryFullPowerDegree47Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block33Norm x).property (boundaryFullPowerDegree47Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block33Norm,boundaryFullPowerDegree47Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x))=c} := by

  have he : ((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x))=(boundaryImPowerRow77_18Degree47Norm x).val+(boundaryImPowerRow77_19Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree47Norm x).property (boundaryImPowerRow77_19Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree47Norm,boundaryImPowerRow77_19Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x))))=(boundaryImPowerRow77_17Degree47Norm x).val+(boundaryFullPowerDegree47Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree47Norm x).property (boundaryFullPowerDegree47Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree47Norm,boundaryFullPowerDegree47Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))=c} := by

  have he : ((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))=(boundaryImPowerRow77_21Degree47Norm x).val+(boundaryLowPowerRow77Degree47Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree47Norm x).property (boundaryLowPowerRow77Degree47Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree47Norm,boundaryLowPowerRow77Degree47Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))=(boundaryImPowerRow77_20Degree47Norm x).val+(boundaryFullPowerDegree47Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree47Norm x).property (boundaryFullPowerDegree47Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree47Norm,boundaryFullPowerDegree47Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))=(boundaryFullPowerDegree47Block38Norm x).val+(boundaryFullPowerDegree47Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block38Norm x).property (boundaryFullPowerDegree47Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block38Norm,boundaryFullPowerDegree47Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))))=(boundaryFullPowerDegree47Block36Norm x).val+(boundaryFullPowerDegree47Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block36Norm x).property (boundaryFullPowerDegree47Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block36Norm,boundaryFullPowerDegree47Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x)))))))))+(((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x)))))))))+(((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))))))=(boundaryFullPowerDegree47Block31Norm x).val+(boundaryFullPowerDegree47Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block31Norm x).property (boundaryFullPowerDegree47Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block31Norm,boundaryFullPowerDegree47Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree47Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x)))))))))+(((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x)))))))))))+(((((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x)))))))))+(((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x)))))))))+(((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x)))))))))))+(((((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x)))))))))+(((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x))))))))))))=(boundaryFullPowerDegree47Block21Norm x).val+(boundaryFullPowerDegree47Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree47Block21Norm x).property (boundaryFullPowerDegree47Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block21Norm,boundaryFullPowerDegree47Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree47Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 47 x=c} := by

  have he0 : boundaryFullPowerRow77 47 x=((((((((((boundaryRePowerRow77_0 47 x)+(boundaryRePowerRow77_1 47 x)))+(((boundaryRePowerRow77_2 47 x)+(((boundaryRePowerRow77_3 47 x)+(boundaryRePowerRow77_4 47 x)))))))+(((((boundaryRePowerRow77_5 47 x)+(((boundaryRePowerRow77_6 47 x)+(boundaryRePowerRow77_7 47 x)))))+(((boundaryRePowerRow77_8 47 x)+(((boundaryRePowerRow77_9 47 x)+(boundaryRePowerRow77_10 47 x)))))))))+(((((((boundaryRePowerRow77_11 47 x)+(((boundaryRePowerRow77_12 47 x)+(boundaryRePowerRow77_13 47 x)))))+(((boundaryRePowerRow77_14 47 x)+(((boundaryRePowerRow77_15 47 x)+(boundaryRePowerRow77_16 47 x)))))))+(((((boundaryRePowerRow77_17 47 x)+(((boundaryRePowerRow77_18 47 x)+(boundaryRePowerRow77_19 47 x)))))+(((boundaryRePowerRow77_20 47 x)+(((boundaryRePowerRow77_21 47 x)+(boundaryRePowerRow77_22 47 x)))))))))))+(((((((((boundaryImPowerRow77_0 47 x)+(boundaryImPowerRow77_1 47 x)))+(((boundaryImPowerRow77_2 47 x)+(((boundaryImPowerRow77_3 47 x)+(boundaryImPowerRow77_4 47 x)))))))+(((((boundaryImPowerRow77_5 47 x)+(((boundaryImPowerRow77_6 47 x)+(boundaryImPowerRow77_7 47 x)))))+(((boundaryImPowerRow77_8 47 x)+(((boundaryImPowerRow77_9 47 x)+(boundaryImPowerRow77_10 47 x)))))))))+(((((((boundaryImPowerRow77_11 47 x)+(((boundaryImPowerRow77_12 47 x)+(boundaryImPowerRow77_13 47 x)))))+(((boundaryImPowerRow77_14 47 x)+(((boundaryImPowerRow77_15 47 x)+(boundaryImPowerRow77_16 47 x)))))))+(((((boundaryImPowerRow77_17 47 x)+(((boundaryImPowerRow77_18 47 x)+(boundaryImPowerRow77_19 47 x)))))+(((boundaryImPowerRow77_20 47 x)+(((boundaryImPowerRow77_21 47 x)+(boundaryLowPowerRow77 47 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree47Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree47Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
