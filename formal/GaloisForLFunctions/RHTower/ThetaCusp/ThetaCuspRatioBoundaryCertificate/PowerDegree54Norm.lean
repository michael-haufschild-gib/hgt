import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree54Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree54Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x))=c} := by

  have he : ((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x))=(boundaryRePowerRow77_0Degree54Norm x).val+(boundaryRePowerRow77_1Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree54Norm x).property (boundaryRePowerRow77_1Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree54Norm,boundaryRePowerRow77_1Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x))=c} := by

  have he : ((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x))=(boundaryRePowerRow77_3Degree54Norm x).val+(boundaryRePowerRow77_4Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree54Norm x).property (boundaryRePowerRow77_4Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree54Norm,boundaryRePowerRow77_4Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x))))=(boundaryRePowerRow77_2Degree54Norm x).val+(boundaryFullPowerDegree54Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree54Norm x).property (boundaryFullPowerDegree54Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree54Norm,boundaryFullPowerDegree54Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x))))))=(boundaryFullPowerDegree54Block0Norm x).val+(boundaryFullPowerDegree54Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block0Norm x).property (boundaryFullPowerDegree54Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block0Norm,boundaryFullPowerDegree54Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x))=c} := by

  have he : ((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x))=(boundaryRePowerRow77_6Degree54Norm x).val+(boundaryRePowerRow77_7Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree54Norm x).property (boundaryRePowerRow77_7Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree54Norm,boundaryRePowerRow77_7Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x))))=(boundaryRePowerRow77_5Degree54Norm x).val+(boundaryFullPowerDegree54Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree54Norm x).property (boundaryFullPowerDegree54Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree54Norm,boundaryFullPowerDegree54Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))=c} := by

  have he : ((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))=(boundaryRePowerRow77_9Degree54Norm x).val+(boundaryRePowerRow77_10Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree54Norm x).property (boundaryRePowerRow77_10Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree54Norm,boundaryRePowerRow77_10Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))))=(boundaryRePowerRow77_8Degree54Norm x).val+(boundaryFullPowerDegree54Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree54Norm x).property (boundaryFullPowerDegree54Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree54Norm,boundaryFullPowerDegree54Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))))))=(boundaryFullPowerDegree54Block5Norm x).val+(boundaryFullPowerDegree54Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block5Norm x).property (boundaryFullPowerDegree54Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block5Norm,boundaryFullPowerDegree54Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x))))))))=(boundaryFullPowerDegree54Block3Norm x).val+(boundaryFullPowerDegree54Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block3Norm x).property (boundaryFullPowerDegree54Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block3Norm,boundaryFullPowerDegree54Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x))=c} := by

  have he : ((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x))=(boundaryRePowerRow77_12Degree54Norm x).val+(boundaryRePowerRow77_13Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree54Norm x).property (boundaryRePowerRow77_13Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree54Norm,boundaryRePowerRow77_13Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x))))=(boundaryRePowerRow77_11Degree54Norm x).val+(boundaryFullPowerDegree54Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree54Norm x).property (boundaryFullPowerDegree54Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree54Norm,boundaryFullPowerDegree54Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x))=c} := by

  have he : ((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x))=(boundaryRePowerRow77_15Degree54Norm x).val+(boundaryRePowerRow77_16Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree54Norm x).property (boundaryRePowerRow77_16Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree54Norm,boundaryRePowerRow77_16Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x))))=(boundaryRePowerRow77_14Degree54Norm x).val+(boundaryFullPowerDegree54Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree54Norm x).property (boundaryFullPowerDegree54Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree54Norm,boundaryFullPowerDegree54Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x))))))=(boundaryFullPowerDegree54Block11Norm x).val+(boundaryFullPowerDegree54Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block11Norm x).property (boundaryFullPowerDegree54Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block11Norm,boundaryFullPowerDegree54Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x))=c} := by

  have he : ((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x))=(boundaryRePowerRow77_18Degree54Norm x).val+(boundaryRePowerRow77_19Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree54Norm x).property (boundaryRePowerRow77_19Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree54Norm,boundaryRePowerRow77_19Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x))))=(boundaryRePowerRow77_17Degree54Norm x).val+(boundaryFullPowerDegree54Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree54Norm x).property (boundaryFullPowerDegree54Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree54Norm,boundaryFullPowerDegree54Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))=c} := by

  have he : ((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))=(boundaryRePowerRow77_21Degree54Norm x).val+(boundaryRePowerRow77_22Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree54Norm x).property (boundaryRePowerRow77_22Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree54Norm,boundaryRePowerRow77_22Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))=(boundaryRePowerRow77_20Degree54Norm x).val+(boundaryFullPowerDegree54Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree54Norm x).property (boundaryFullPowerDegree54Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree54Norm,boundaryFullPowerDegree54Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))))=(boundaryFullPowerDegree54Block16Norm x).val+(boundaryFullPowerDegree54Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block16Norm x).property (boundaryFullPowerDegree54Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block16Norm,boundaryFullPowerDegree54Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))))))=(boundaryFullPowerDegree54Block14Norm x).val+(boundaryFullPowerDegree54Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block14Norm x).property (boundaryFullPowerDegree54Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block14Norm,boundaryFullPowerDegree54Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x)))))))))+(((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x)))))))))+(((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x))))))))))=(boundaryFullPowerDegree54Block9Norm x).val+(boundaryFullPowerDegree54Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block9Norm x).property (boundaryFullPowerDegree54Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block9Norm,boundaryFullPowerDegree54Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x))=c} := by

  have he : ((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x))=(boundaryImPowerRow77_0Degree54Norm x).val+(boundaryImPowerRow77_1Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree54Norm x).property (boundaryImPowerRow77_1Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree54Norm,boundaryImPowerRow77_1Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x))=c} := by

  have he : ((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x))=(boundaryImPowerRow77_3Degree54Norm x).val+(boundaryImPowerRow77_4Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree54Norm x).property (boundaryImPowerRow77_4Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree54Norm,boundaryImPowerRow77_4Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x))))=(boundaryImPowerRow77_2Degree54Norm x).val+(boundaryFullPowerDegree54Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree54Norm x).property (boundaryFullPowerDegree54Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree54Norm,boundaryFullPowerDegree54Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x))))))=(boundaryFullPowerDegree54Block22Norm x).val+(boundaryFullPowerDegree54Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block22Norm x).property (boundaryFullPowerDegree54Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block22Norm,boundaryFullPowerDegree54Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x))=c} := by

  have he : ((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x))=(boundaryImPowerRow77_6Degree54Norm x).val+(boundaryImPowerRow77_7Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree54Norm x).property (boundaryImPowerRow77_7Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree54Norm,boundaryImPowerRow77_7Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x))))=(boundaryImPowerRow77_5Degree54Norm x).val+(boundaryFullPowerDegree54Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree54Norm x).property (boundaryFullPowerDegree54Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree54Norm,boundaryFullPowerDegree54Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))=c} := by

  have he : ((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))=(boundaryImPowerRow77_9Degree54Norm x).val+(boundaryImPowerRow77_10Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree54Norm x).property (boundaryImPowerRow77_10Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree54Norm,boundaryImPowerRow77_10Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))))=(boundaryImPowerRow77_8Degree54Norm x).val+(boundaryFullPowerDegree54Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree54Norm x).property (boundaryFullPowerDegree54Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree54Norm,boundaryFullPowerDegree54Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))))))=(boundaryFullPowerDegree54Block27Norm x).val+(boundaryFullPowerDegree54Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block27Norm x).property (boundaryFullPowerDegree54Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block27Norm,boundaryFullPowerDegree54Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x))))))))=(boundaryFullPowerDegree54Block25Norm x).val+(boundaryFullPowerDegree54Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block25Norm x).property (boundaryFullPowerDegree54Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block25Norm,boundaryFullPowerDegree54Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x))=c} := by

  have he : ((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x))=(boundaryImPowerRow77_12Degree54Norm x).val+(boundaryImPowerRow77_13Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree54Norm x).property (boundaryImPowerRow77_13Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree54Norm,boundaryImPowerRow77_13Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x))))=(boundaryImPowerRow77_11Degree54Norm x).val+(boundaryFullPowerDegree54Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree54Norm x).property (boundaryFullPowerDegree54Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree54Norm,boundaryFullPowerDegree54Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x))=c} := by

  have he : ((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x))=(boundaryImPowerRow77_15Degree54Norm x).val+(boundaryImPowerRow77_16Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree54Norm x).property (boundaryImPowerRow77_16Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree54Norm,boundaryImPowerRow77_16Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x))))=(boundaryImPowerRow77_14Degree54Norm x).val+(boundaryFullPowerDegree54Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree54Norm x).property (boundaryFullPowerDegree54Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree54Norm,boundaryFullPowerDegree54Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x))))))=(boundaryFullPowerDegree54Block33Norm x).val+(boundaryFullPowerDegree54Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block33Norm x).property (boundaryFullPowerDegree54Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block33Norm,boundaryFullPowerDegree54Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x))=c} := by

  have he : ((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x))=(boundaryImPowerRow77_18Degree54Norm x).val+(boundaryImPowerRow77_19Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree54Norm x).property (boundaryImPowerRow77_19Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree54Norm,boundaryImPowerRow77_19Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x))))=(boundaryImPowerRow77_17Degree54Norm x).val+(boundaryFullPowerDegree54Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree54Norm x).property (boundaryFullPowerDegree54Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree54Norm,boundaryFullPowerDegree54Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))=c} := by

  have he : ((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))=(boundaryImPowerRow77_21Degree54Norm x).val+(boundaryLowPowerRow77Degree54Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree54Norm x).property (boundaryLowPowerRow77Degree54Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree54Norm,boundaryLowPowerRow77Degree54Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))=(boundaryImPowerRow77_20Degree54Norm x).val+(boundaryFullPowerDegree54Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree54Norm x).property (boundaryFullPowerDegree54Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree54Norm,boundaryFullPowerDegree54Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))=(boundaryFullPowerDegree54Block38Norm x).val+(boundaryFullPowerDegree54Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block38Norm x).property (boundaryFullPowerDegree54Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block38Norm,boundaryFullPowerDegree54Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))))=(boundaryFullPowerDegree54Block36Norm x).val+(boundaryFullPowerDegree54Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block36Norm x).property (boundaryFullPowerDegree54Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block36Norm,boundaryFullPowerDegree54Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x)))))))))+(((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x)))))))))+(((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))))))=(boundaryFullPowerDegree54Block31Norm x).val+(boundaryFullPowerDegree54Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block31Norm x).property (boundaryFullPowerDegree54Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block31Norm,boundaryFullPowerDegree54Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree54Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x)))))))))+(((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x)))))))))))+(((((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x)))))))))+(((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x)))))))))+(((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x)))))))))))+(((((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x)))))))))+(((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x))))))))))))=(boundaryFullPowerDegree54Block21Norm x).val+(boundaryFullPowerDegree54Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree54Block21Norm x).property (boundaryFullPowerDegree54Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block21Norm,boundaryFullPowerDegree54Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree54Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 54 x=c} := by

  have he0 : boundaryFullPowerRow77 54 x=((((((((((boundaryRePowerRow77_0 54 x)+(boundaryRePowerRow77_1 54 x)))+(((boundaryRePowerRow77_2 54 x)+(((boundaryRePowerRow77_3 54 x)+(boundaryRePowerRow77_4 54 x)))))))+(((((boundaryRePowerRow77_5 54 x)+(((boundaryRePowerRow77_6 54 x)+(boundaryRePowerRow77_7 54 x)))))+(((boundaryRePowerRow77_8 54 x)+(((boundaryRePowerRow77_9 54 x)+(boundaryRePowerRow77_10 54 x)))))))))+(((((((boundaryRePowerRow77_11 54 x)+(((boundaryRePowerRow77_12 54 x)+(boundaryRePowerRow77_13 54 x)))))+(((boundaryRePowerRow77_14 54 x)+(((boundaryRePowerRow77_15 54 x)+(boundaryRePowerRow77_16 54 x)))))))+(((((boundaryRePowerRow77_17 54 x)+(((boundaryRePowerRow77_18 54 x)+(boundaryRePowerRow77_19 54 x)))))+(((boundaryRePowerRow77_20 54 x)+(((boundaryRePowerRow77_21 54 x)+(boundaryRePowerRow77_22 54 x)))))))))))+(((((((((boundaryImPowerRow77_0 54 x)+(boundaryImPowerRow77_1 54 x)))+(((boundaryImPowerRow77_2 54 x)+(((boundaryImPowerRow77_3 54 x)+(boundaryImPowerRow77_4 54 x)))))))+(((((boundaryImPowerRow77_5 54 x)+(((boundaryImPowerRow77_6 54 x)+(boundaryImPowerRow77_7 54 x)))))+(((boundaryImPowerRow77_8 54 x)+(((boundaryImPowerRow77_9 54 x)+(boundaryImPowerRow77_10 54 x)))))))))+(((((((boundaryImPowerRow77_11 54 x)+(((boundaryImPowerRow77_12 54 x)+(boundaryImPowerRow77_13 54 x)))))+(((boundaryImPowerRow77_14 54 x)+(((boundaryImPowerRow77_15 54 x)+(boundaryImPowerRow77_16 54 x)))))))+(((((boundaryImPowerRow77_17 54 x)+(((boundaryImPowerRow77_18 54 x)+(boundaryImPowerRow77_19 54 x)))))+(((boundaryImPowerRow77_20 54 x)+(((boundaryImPowerRow77_21 54 x)+(boundaryLowPowerRow77 54 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree54Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree54Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
