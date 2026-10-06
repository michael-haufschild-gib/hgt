import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree17Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree17Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x))=c} := by

  have he : ((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x))=(boundaryRePowerRow77_0Degree17Norm x).val+(boundaryRePowerRow77_1Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree17Norm x).property (boundaryRePowerRow77_1Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree17Norm,boundaryRePowerRow77_1Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x))=c} := by

  have he : ((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x))=(boundaryRePowerRow77_3Degree17Norm x).val+(boundaryRePowerRow77_4Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree17Norm x).property (boundaryRePowerRow77_4Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree17Norm,boundaryRePowerRow77_4Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x))))=(boundaryRePowerRow77_2Degree17Norm x).val+(boundaryFullPowerDegree17Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree17Norm x).property (boundaryFullPowerDegree17Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree17Norm,boundaryFullPowerDegree17Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x))))))=(boundaryFullPowerDegree17Block0Norm x).val+(boundaryFullPowerDegree17Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block0Norm x).property (boundaryFullPowerDegree17Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block0Norm,boundaryFullPowerDegree17Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x))=c} := by

  have he : ((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x))=(boundaryRePowerRow77_6Degree17Norm x).val+(boundaryRePowerRow77_7Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree17Norm x).property (boundaryRePowerRow77_7Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree17Norm,boundaryRePowerRow77_7Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x))))=(boundaryRePowerRow77_5Degree17Norm x).val+(boundaryFullPowerDegree17Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree17Norm x).property (boundaryFullPowerDegree17Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree17Norm,boundaryFullPowerDegree17Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))=c} := by

  have he : ((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))=(boundaryRePowerRow77_9Degree17Norm x).val+(boundaryRePowerRow77_10Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree17Norm x).property (boundaryRePowerRow77_10Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree17Norm,boundaryRePowerRow77_10Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))))=(boundaryRePowerRow77_8Degree17Norm x).val+(boundaryFullPowerDegree17Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree17Norm x).property (boundaryFullPowerDegree17Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree17Norm,boundaryFullPowerDegree17Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))))))=(boundaryFullPowerDegree17Block5Norm x).val+(boundaryFullPowerDegree17Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block5Norm x).property (boundaryFullPowerDegree17Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block5Norm,boundaryFullPowerDegree17Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x))))))))=(boundaryFullPowerDegree17Block3Norm x).val+(boundaryFullPowerDegree17Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block3Norm x).property (boundaryFullPowerDegree17Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block3Norm,boundaryFullPowerDegree17Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x))=c} := by

  have he : ((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x))=(boundaryRePowerRow77_12Degree17Norm x).val+(boundaryRePowerRow77_13Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree17Norm x).property (boundaryRePowerRow77_13Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree17Norm,boundaryRePowerRow77_13Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x))))=(boundaryRePowerRow77_11Degree17Norm x).val+(boundaryFullPowerDegree17Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree17Norm x).property (boundaryFullPowerDegree17Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree17Norm,boundaryFullPowerDegree17Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x))=c} := by

  have he : ((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x))=(boundaryRePowerRow77_15Degree17Norm x).val+(boundaryRePowerRow77_16Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree17Norm x).property (boundaryRePowerRow77_16Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree17Norm,boundaryRePowerRow77_16Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x))))=(boundaryRePowerRow77_14Degree17Norm x).val+(boundaryFullPowerDegree17Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree17Norm x).property (boundaryFullPowerDegree17Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree17Norm,boundaryFullPowerDegree17Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x))))))=(boundaryFullPowerDegree17Block11Norm x).val+(boundaryFullPowerDegree17Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block11Norm x).property (boundaryFullPowerDegree17Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block11Norm,boundaryFullPowerDegree17Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x))=c} := by

  have he : ((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x))=(boundaryRePowerRow77_18Degree17Norm x).val+(boundaryRePowerRow77_19Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree17Norm x).property (boundaryRePowerRow77_19Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree17Norm,boundaryRePowerRow77_19Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x))))=(boundaryRePowerRow77_17Degree17Norm x).val+(boundaryFullPowerDegree17Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree17Norm x).property (boundaryFullPowerDegree17Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree17Norm,boundaryFullPowerDegree17Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))=c} := by

  have he : ((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))=(boundaryRePowerRow77_21Degree17Norm x).val+(boundaryRePowerRow77_22Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree17Norm x).property (boundaryRePowerRow77_22Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree17Norm,boundaryRePowerRow77_22Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))=(boundaryRePowerRow77_20Degree17Norm x).val+(boundaryFullPowerDegree17Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree17Norm x).property (boundaryFullPowerDegree17Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree17Norm,boundaryFullPowerDegree17Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))))=(boundaryFullPowerDegree17Block16Norm x).val+(boundaryFullPowerDegree17Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block16Norm x).property (boundaryFullPowerDegree17Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block16Norm,boundaryFullPowerDegree17Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))))))=(boundaryFullPowerDegree17Block14Norm x).val+(boundaryFullPowerDegree17Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block14Norm x).property (boundaryFullPowerDegree17Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block14Norm,boundaryFullPowerDegree17Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x)))))))))+(((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x)))))))))+(((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x))))))))))=(boundaryFullPowerDegree17Block9Norm x).val+(boundaryFullPowerDegree17Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block9Norm x).property (boundaryFullPowerDegree17Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block9Norm,boundaryFullPowerDegree17Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x))=c} := by

  have he : ((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x))=(boundaryImPowerRow77_0Degree17Norm x).val+(boundaryImPowerRow77_1Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree17Norm x).property (boundaryImPowerRow77_1Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree17Norm,boundaryImPowerRow77_1Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x))=c} := by

  have he : ((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x))=(boundaryImPowerRow77_3Degree17Norm x).val+(boundaryImPowerRow77_4Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree17Norm x).property (boundaryImPowerRow77_4Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree17Norm,boundaryImPowerRow77_4Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x))))=(boundaryImPowerRow77_2Degree17Norm x).val+(boundaryFullPowerDegree17Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree17Norm x).property (boundaryFullPowerDegree17Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree17Norm,boundaryFullPowerDegree17Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x))))))=(boundaryFullPowerDegree17Block22Norm x).val+(boundaryFullPowerDegree17Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block22Norm x).property (boundaryFullPowerDegree17Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block22Norm,boundaryFullPowerDegree17Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x))=c} := by

  have he : ((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x))=(boundaryImPowerRow77_6Degree17Norm x).val+(boundaryImPowerRow77_7Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree17Norm x).property (boundaryImPowerRow77_7Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree17Norm,boundaryImPowerRow77_7Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x))))=(boundaryImPowerRow77_5Degree17Norm x).val+(boundaryFullPowerDegree17Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree17Norm x).property (boundaryFullPowerDegree17Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree17Norm,boundaryFullPowerDegree17Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))=c} := by

  have he : ((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))=(boundaryImPowerRow77_9Degree17Norm x).val+(boundaryImPowerRow77_10Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree17Norm x).property (boundaryImPowerRow77_10Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree17Norm,boundaryImPowerRow77_10Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))))=(boundaryImPowerRow77_8Degree17Norm x).val+(boundaryFullPowerDegree17Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree17Norm x).property (boundaryFullPowerDegree17Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree17Norm,boundaryFullPowerDegree17Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))))))=(boundaryFullPowerDegree17Block27Norm x).val+(boundaryFullPowerDegree17Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block27Norm x).property (boundaryFullPowerDegree17Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block27Norm,boundaryFullPowerDegree17Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x))))))))=(boundaryFullPowerDegree17Block25Norm x).val+(boundaryFullPowerDegree17Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block25Norm x).property (boundaryFullPowerDegree17Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block25Norm,boundaryFullPowerDegree17Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x))=c} := by

  have he : ((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x))=(boundaryImPowerRow77_12Degree17Norm x).val+(boundaryImPowerRow77_13Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree17Norm x).property (boundaryImPowerRow77_13Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree17Norm,boundaryImPowerRow77_13Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x))))=(boundaryImPowerRow77_11Degree17Norm x).val+(boundaryFullPowerDegree17Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree17Norm x).property (boundaryFullPowerDegree17Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree17Norm,boundaryFullPowerDegree17Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x))=c} := by

  have he : ((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x))=(boundaryImPowerRow77_15Degree17Norm x).val+(boundaryImPowerRow77_16Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree17Norm x).property (boundaryImPowerRow77_16Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree17Norm,boundaryImPowerRow77_16Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x))))=(boundaryImPowerRow77_14Degree17Norm x).val+(boundaryFullPowerDegree17Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree17Norm x).property (boundaryFullPowerDegree17Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree17Norm,boundaryFullPowerDegree17Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x))))))=(boundaryFullPowerDegree17Block33Norm x).val+(boundaryFullPowerDegree17Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block33Norm x).property (boundaryFullPowerDegree17Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block33Norm,boundaryFullPowerDegree17Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x))=c} := by

  have he : ((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x))=(boundaryImPowerRow77_18Degree17Norm x).val+(boundaryImPowerRow77_19Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree17Norm x).property (boundaryImPowerRow77_19Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree17Norm,boundaryImPowerRow77_19Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x))))=(boundaryImPowerRow77_17Degree17Norm x).val+(boundaryFullPowerDegree17Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree17Norm x).property (boundaryFullPowerDegree17Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree17Norm,boundaryFullPowerDegree17Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))=c} := by

  have he : ((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))=(boundaryImPowerRow77_21Degree17Norm x).val+(boundaryLowPowerRow77Degree17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree17Norm x).property (boundaryLowPowerRow77Degree17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree17Norm,boundaryLowPowerRow77Degree17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))=(boundaryImPowerRow77_20Degree17Norm x).val+(boundaryFullPowerDegree17Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree17Norm x).property (boundaryFullPowerDegree17Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree17Norm,boundaryFullPowerDegree17Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))=(boundaryFullPowerDegree17Block38Norm x).val+(boundaryFullPowerDegree17Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block38Norm x).property (boundaryFullPowerDegree17Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block38Norm,boundaryFullPowerDegree17Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))))=(boundaryFullPowerDegree17Block36Norm x).val+(boundaryFullPowerDegree17Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block36Norm x).property (boundaryFullPowerDegree17Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block36Norm,boundaryFullPowerDegree17Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x)))))))))+(((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x)))))))))+(((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))))))=(boundaryFullPowerDegree17Block31Norm x).val+(boundaryFullPowerDegree17Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block31Norm x).property (boundaryFullPowerDegree17Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block31Norm,boundaryFullPowerDegree17Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree17Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x)))))))))+(((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x)))))))))))+(((((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x)))))))))+(((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x)))))))))+(((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x)))))))))))+(((((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x)))))))))+(((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x))))))))))))=(boundaryFullPowerDegree17Block21Norm x).val+(boundaryFullPowerDegree17Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree17Block21Norm x).property (boundaryFullPowerDegree17Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block21Norm,boundaryFullPowerDegree17Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree17Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 17 x=c} := by

  have he0 : boundaryFullPowerRow77 17 x=((((((((((boundaryRePowerRow77_0 17 x)+(boundaryRePowerRow77_1 17 x)))+(((boundaryRePowerRow77_2 17 x)+(((boundaryRePowerRow77_3 17 x)+(boundaryRePowerRow77_4 17 x)))))))+(((((boundaryRePowerRow77_5 17 x)+(((boundaryRePowerRow77_6 17 x)+(boundaryRePowerRow77_7 17 x)))))+(((boundaryRePowerRow77_8 17 x)+(((boundaryRePowerRow77_9 17 x)+(boundaryRePowerRow77_10 17 x)))))))))+(((((((boundaryRePowerRow77_11 17 x)+(((boundaryRePowerRow77_12 17 x)+(boundaryRePowerRow77_13 17 x)))))+(((boundaryRePowerRow77_14 17 x)+(((boundaryRePowerRow77_15 17 x)+(boundaryRePowerRow77_16 17 x)))))))+(((((boundaryRePowerRow77_17 17 x)+(((boundaryRePowerRow77_18 17 x)+(boundaryRePowerRow77_19 17 x)))))+(((boundaryRePowerRow77_20 17 x)+(((boundaryRePowerRow77_21 17 x)+(boundaryRePowerRow77_22 17 x)))))))))))+(((((((((boundaryImPowerRow77_0 17 x)+(boundaryImPowerRow77_1 17 x)))+(((boundaryImPowerRow77_2 17 x)+(((boundaryImPowerRow77_3 17 x)+(boundaryImPowerRow77_4 17 x)))))))+(((((boundaryImPowerRow77_5 17 x)+(((boundaryImPowerRow77_6 17 x)+(boundaryImPowerRow77_7 17 x)))))+(((boundaryImPowerRow77_8 17 x)+(((boundaryImPowerRow77_9 17 x)+(boundaryImPowerRow77_10 17 x)))))))))+(((((((boundaryImPowerRow77_11 17 x)+(((boundaryImPowerRow77_12 17 x)+(boundaryImPowerRow77_13 17 x)))))+(((boundaryImPowerRow77_14 17 x)+(((boundaryImPowerRow77_15 17 x)+(boundaryImPowerRow77_16 17 x)))))))+(((((boundaryImPowerRow77_17 17 x)+(((boundaryImPowerRow77_18 17 x)+(boundaryImPowerRow77_19 17 x)))))+(((boundaryImPowerRow77_20 17 x)+(((boundaryImPowerRow77_21 17 x)+(boundaryLowPowerRow77 17 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree17Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree17Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
