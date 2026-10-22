import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree94Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree94Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x))=c} := by

  have he : ((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x))=(boundaryRePowerRow77_0Degree94Norm x).val+(boundaryRePowerRow77_1Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree94Norm x).property (boundaryRePowerRow77_1Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree94Norm,boundaryRePowerRow77_1Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x))=c} := by

  have he : ((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x))=(boundaryRePowerRow77_3Degree94Norm x).val+(boundaryRePowerRow77_4Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree94Norm x).property (boundaryRePowerRow77_4Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree94Norm,boundaryRePowerRow77_4Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x))))=(boundaryRePowerRow77_2Degree94Norm x).val+(boundaryFullPowerDegree94Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree94Norm x).property (boundaryFullPowerDegree94Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree94Norm,boundaryFullPowerDegree94Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x))))))=(boundaryFullPowerDegree94Block0Norm x).val+(boundaryFullPowerDegree94Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block0Norm x).property (boundaryFullPowerDegree94Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block0Norm,boundaryFullPowerDegree94Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x))=c} := by

  have he : ((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x))=(boundaryRePowerRow77_6Degree94Norm x).val+(boundaryRePowerRow77_7Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree94Norm x).property (boundaryRePowerRow77_7Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree94Norm,boundaryRePowerRow77_7Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x))))=(boundaryRePowerRow77_5Degree94Norm x).val+(boundaryFullPowerDegree94Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree94Norm x).property (boundaryFullPowerDegree94Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree94Norm,boundaryFullPowerDegree94Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))=c} := by

  have he : ((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))=(boundaryRePowerRow77_9Degree94Norm x).val+(boundaryRePowerRow77_10Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree94Norm x).property (boundaryRePowerRow77_10Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree94Norm,boundaryRePowerRow77_10Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))))=(boundaryRePowerRow77_8Degree94Norm x).val+(boundaryFullPowerDegree94Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree94Norm x).property (boundaryFullPowerDegree94Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree94Norm,boundaryFullPowerDegree94Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))))))=(boundaryFullPowerDegree94Block5Norm x).val+(boundaryFullPowerDegree94Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block5Norm x).property (boundaryFullPowerDegree94Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block5Norm,boundaryFullPowerDegree94Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x))))))))=(boundaryFullPowerDegree94Block3Norm x).val+(boundaryFullPowerDegree94Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block3Norm x).property (boundaryFullPowerDegree94Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block3Norm,boundaryFullPowerDegree94Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x))=c} := by

  have he : ((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x))=(boundaryRePowerRow77_12Degree94Norm x).val+(boundaryRePowerRow77_13Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree94Norm x).property (boundaryRePowerRow77_13Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree94Norm,boundaryRePowerRow77_13Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x))))=(boundaryRePowerRow77_11Degree94Norm x).val+(boundaryFullPowerDegree94Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree94Norm x).property (boundaryFullPowerDegree94Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree94Norm,boundaryFullPowerDegree94Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x))=c} := by

  have he : ((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x))=(boundaryRePowerRow77_15Degree94Norm x).val+(boundaryRePowerRow77_16Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree94Norm x).property (boundaryRePowerRow77_16Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree94Norm,boundaryRePowerRow77_16Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x))))=(boundaryRePowerRow77_14Degree94Norm x).val+(boundaryFullPowerDegree94Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree94Norm x).property (boundaryFullPowerDegree94Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree94Norm,boundaryFullPowerDegree94Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x))))))=(boundaryFullPowerDegree94Block11Norm x).val+(boundaryFullPowerDegree94Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block11Norm x).property (boundaryFullPowerDegree94Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block11Norm,boundaryFullPowerDegree94Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x))=c} := by

  have he : ((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x))=(boundaryRePowerRow77_18Degree94Norm x).val+(boundaryRePowerRow77_19Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree94Norm x).property (boundaryRePowerRow77_19Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree94Norm,boundaryRePowerRow77_19Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x))))=(boundaryRePowerRow77_17Degree94Norm x).val+(boundaryFullPowerDegree94Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree94Norm x).property (boundaryFullPowerDegree94Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree94Norm,boundaryFullPowerDegree94Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))=c} := by

  have he : ((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))=(boundaryRePowerRow77_21Degree94Norm x).val+(boundaryRePowerRow77_22Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree94Norm x).property (boundaryRePowerRow77_22Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree94Norm,boundaryRePowerRow77_22Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))=(boundaryRePowerRow77_20Degree94Norm x).val+(boundaryFullPowerDegree94Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree94Norm x).property (boundaryFullPowerDegree94Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree94Norm,boundaryFullPowerDegree94Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))))=(boundaryFullPowerDegree94Block16Norm x).val+(boundaryFullPowerDegree94Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block16Norm x).property (boundaryFullPowerDegree94Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block16Norm,boundaryFullPowerDegree94Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))))))=(boundaryFullPowerDegree94Block14Norm x).val+(boundaryFullPowerDegree94Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block14Norm x).property (boundaryFullPowerDegree94Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block14Norm,boundaryFullPowerDegree94Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x)))))))))+(((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x)))))))))+(((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x))))))))))=(boundaryFullPowerDegree94Block9Norm x).val+(boundaryFullPowerDegree94Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block9Norm x).property (boundaryFullPowerDegree94Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block9Norm,boundaryFullPowerDegree94Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x))=c} := by

  have he : ((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x))=(boundaryImPowerRow77_0Degree94Norm x).val+(boundaryImPowerRow77_1Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree94Norm x).property (boundaryImPowerRow77_1Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree94Norm,boundaryImPowerRow77_1Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x))=c} := by

  have he : ((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x))=(boundaryImPowerRow77_3Degree94Norm x).val+(boundaryImPowerRow77_4Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree94Norm x).property (boundaryImPowerRow77_4Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree94Norm,boundaryImPowerRow77_4Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x))))=(boundaryImPowerRow77_2Degree94Norm x).val+(boundaryFullPowerDegree94Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree94Norm x).property (boundaryFullPowerDegree94Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree94Norm,boundaryFullPowerDegree94Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x))))))=(boundaryFullPowerDegree94Block22Norm x).val+(boundaryFullPowerDegree94Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block22Norm x).property (boundaryFullPowerDegree94Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block22Norm,boundaryFullPowerDegree94Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x))=c} := by

  have he : ((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x))=(boundaryImPowerRow77_6Degree94Norm x).val+(boundaryImPowerRow77_7Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree94Norm x).property (boundaryImPowerRow77_7Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree94Norm,boundaryImPowerRow77_7Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x))))=(boundaryImPowerRow77_5Degree94Norm x).val+(boundaryFullPowerDegree94Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree94Norm x).property (boundaryFullPowerDegree94Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree94Norm,boundaryFullPowerDegree94Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))=c} := by

  have he : ((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))=(boundaryImPowerRow77_9Degree94Norm x).val+(boundaryImPowerRow77_10Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree94Norm x).property (boundaryImPowerRow77_10Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree94Norm,boundaryImPowerRow77_10Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))))=(boundaryImPowerRow77_8Degree94Norm x).val+(boundaryFullPowerDegree94Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree94Norm x).property (boundaryFullPowerDegree94Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree94Norm,boundaryFullPowerDegree94Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))))))=(boundaryFullPowerDegree94Block27Norm x).val+(boundaryFullPowerDegree94Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block27Norm x).property (boundaryFullPowerDegree94Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block27Norm,boundaryFullPowerDegree94Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x))))))))=(boundaryFullPowerDegree94Block25Norm x).val+(boundaryFullPowerDegree94Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block25Norm x).property (boundaryFullPowerDegree94Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block25Norm,boundaryFullPowerDegree94Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x))=c} := by

  have he : ((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x))=(boundaryImPowerRow77_12Degree94Norm x).val+(boundaryImPowerRow77_13Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree94Norm x).property (boundaryImPowerRow77_13Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree94Norm,boundaryImPowerRow77_13Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x))))=(boundaryImPowerRow77_11Degree94Norm x).val+(boundaryFullPowerDegree94Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree94Norm x).property (boundaryFullPowerDegree94Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree94Norm,boundaryFullPowerDegree94Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x))=c} := by

  have he : ((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x))=(boundaryImPowerRow77_15Degree94Norm x).val+(boundaryImPowerRow77_16Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree94Norm x).property (boundaryImPowerRow77_16Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree94Norm,boundaryImPowerRow77_16Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x))))=(boundaryImPowerRow77_14Degree94Norm x).val+(boundaryFullPowerDegree94Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree94Norm x).property (boundaryFullPowerDegree94Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree94Norm,boundaryFullPowerDegree94Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x))))))=(boundaryFullPowerDegree94Block33Norm x).val+(boundaryFullPowerDegree94Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block33Norm x).property (boundaryFullPowerDegree94Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block33Norm,boundaryFullPowerDegree94Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x))=c} := by

  have he : ((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x))=(boundaryImPowerRow77_18Degree94Norm x).val+(boundaryImPowerRow77_19Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree94Norm x).property (boundaryImPowerRow77_19Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree94Norm,boundaryImPowerRow77_19Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x))))=(boundaryImPowerRow77_17Degree94Norm x).val+(boundaryFullPowerDegree94Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree94Norm x).property (boundaryFullPowerDegree94Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree94Norm,boundaryFullPowerDegree94Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))=c} := by

  have he : ((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))=(boundaryImPowerRow77_21Degree94Norm x).val+(boundaryLowPowerRow77Degree94Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree94Norm x).property (boundaryLowPowerRow77Degree94Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree94Norm,boundaryLowPowerRow77Degree94Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))=(boundaryImPowerRow77_20Degree94Norm x).val+(boundaryFullPowerDegree94Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree94Norm x).property (boundaryFullPowerDegree94Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree94Norm,boundaryFullPowerDegree94Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))=(boundaryFullPowerDegree94Block38Norm x).val+(boundaryFullPowerDegree94Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block38Norm x).property (boundaryFullPowerDegree94Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block38Norm,boundaryFullPowerDegree94Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))))=(boundaryFullPowerDegree94Block36Norm x).val+(boundaryFullPowerDegree94Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block36Norm x).property (boundaryFullPowerDegree94Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block36Norm,boundaryFullPowerDegree94Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x)))))))))+(((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x)))))))))+(((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))))))=(boundaryFullPowerDegree94Block31Norm x).val+(boundaryFullPowerDegree94Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block31Norm x).property (boundaryFullPowerDegree94Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block31Norm,boundaryFullPowerDegree94Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree94Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x)))))))))+(((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x)))))))))))+(((((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x)))))))))+(((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x)))))))))+(((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x)))))))))))+(((((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x)))))))))+(((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x))))))))))))=(boundaryFullPowerDegree94Block21Norm x).val+(boundaryFullPowerDegree94Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree94Block21Norm x).property (boundaryFullPowerDegree94Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block21Norm,boundaryFullPowerDegree94Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree94Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 94 x=c} := by

  have he0 : boundaryFullPowerRow77 94 x=((((((((((boundaryRePowerRow77_0 94 x)+(boundaryRePowerRow77_1 94 x)))+(((boundaryRePowerRow77_2 94 x)+(((boundaryRePowerRow77_3 94 x)+(boundaryRePowerRow77_4 94 x)))))))+(((((boundaryRePowerRow77_5 94 x)+(((boundaryRePowerRow77_6 94 x)+(boundaryRePowerRow77_7 94 x)))))+(((boundaryRePowerRow77_8 94 x)+(((boundaryRePowerRow77_9 94 x)+(boundaryRePowerRow77_10 94 x)))))))))+(((((((boundaryRePowerRow77_11 94 x)+(((boundaryRePowerRow77_12 94 x)+(boundaryRePowerRow77_13 94 x)))))+(((boundaryRePowerRow77_14 94 x)+(((boundaryRePowerRow77_15 94 x)+(boundaryRePowerRow77_16 94 x)))))))+(((((boundaryRePowerRow77_17 94 x)+(((boundaryRePowerRow77_18 94 x)+(boundaryRePowerRow77_19 94 x)))))+(((boundaryRePowerRow77_20 94 x)+(((boundaryRePowerRow77_21 94 x)+(boundaryRePowerRow77_22 94 x)))))))))))+(((((((((boundaryImPowerRow77_0 94 x)+(boundaryImPowerRow77_1 94 x)))+(((boundaryImPowerRow77_2 94 x)+(((boundaryImPowerRow77_3 94 x)+(boundaryImPowerRow77_4 94 x)))))))+(((((boundaryImPowerRow77_5 94 x)+(((boundaryImPowerRow77_6 94 x)+(boundaryImPowerRow77_7 94 x)))))+(((boundaryImPowerRow77_8 94 x)+(((boundaryImPowerRow77_9 94 x)+(boundaryImPowerRow77_10 94 x)))))))))+(((((((boundaryImPowerRow77_11 94 x)+(((boundaryImPowerRow77_12 94 x)+(boundaryImPowerRow77_13 94 x)))))+(((boundaryImPowerRow77_14 94 x)+(((boundaryImPowerRow77_15 94 x)+(boundaryImPowerRow77_16 94 x)))))))+(((((boundaryImPowerRow77_17 94 x)+(((boundaryImPowerRow77_18 94 x)+(boundaryImPowerRow77_19 94 x)))))+(((boundaryImPowerRow77_20 94 x)+(((boundaryImPowerRow77_21 94 x)+(boundaryLowPowerRow77 94 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree94Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree94Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
