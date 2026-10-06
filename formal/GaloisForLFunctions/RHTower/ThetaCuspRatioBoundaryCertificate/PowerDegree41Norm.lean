import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree41Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree41Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x))=c} := by

  have he : ((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x))=(boundaryRePowerRow77_0Degree41Norm x).val+(boundaryRePowerRow77_1Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree41Norm x).property (boundaryRePowerRow77_1Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree41Norm,boundaryRePowerRow77_1Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x))=c} := by

  have he : ((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x))=(boundaryRePowerRow77_3Degree41Norm x).val+(boundaryRePowerRow77_4Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree41Norm x).property (boundaryRePowerRow77_4Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree41Norm,boundaryRePowerRow77_4Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x))))=(boundaryRePowerRow77_2Degree41Norm x).val+(boundaryFullPowerDegree41Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree41Norm x).property (boundaryFullPowerDegree41Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree41Norm,boundaryFullPowerDegree41Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x))))))=(boundaryFullPowerDegree41Block0Norm x).val+(boundaryFullPowerDegree41Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block0Norm x).property (boundaryFullPowerDegree41Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block0Norm,boundaryFullPowerDegree41Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x))=c} := by

  have he : ((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x))=(boundaryRePowerRow77_6Degree41Norm x).val+(boundaryRePowerRow77_7Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree41Norm x).property (boundaryRePowerRow77_7Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree41Norm,boundaryRePowerRow77_7Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x))))=(boundaryRePowerRow77_5Degree41Norm x).val+(boundaryFullPowerDegree41Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree41Norm x).property (boundaryFullPowerDegree41Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree41Norm,boundaryFullPowerDegree41Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))=c} := by

  have he : ((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))=(boundaryRePowerRow77_9Degree41Norm x).val+(boundaryRePowerRow77_10Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree41Norm x).property (boundaryRePowerRow77_10Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree41Norm,boundaryRePowerRow77_10Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))))=(boundaryRePowerRow77_8Degree41Norm x).val+(boundaryFullPowerDegree41Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree41Norm x).property (boundaryFullPowerDegree41Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree41Norm,boundaryFullPowerDegree41Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))))))=(boundaryFullPowerDegree41Block5Norm x).val+(boundaryFullPowerDegree41Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block5Norm x).property (boundaryFullPowerDegree41Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block5Norm,boundaryFullPowerDegree41Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x))))))))=(boundaryFullPowerDegree41Block3Norm x).val+(boundaryFullPowerDegree41Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block3Norm x).property (boundaryFullPowerDegree41Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block3Norm,boundaryFullPowerDegree41Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x))=c} := by

  have he : ((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x))=(boundaryRePowerRow77_12Degree41Norm x).val+(boundaryRePowerRow77_13Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree41Norm x).property (boundaryRePowerRow77_13Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree41Norm,boundaryRePowerRow77_13Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x))))=(boundaryRePowerRow77_11Degree41Norm x).val+(boundaryFullPowerDegree41Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree41Norm x).property (boundaryFullPowerDegree41Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree41Norm,boundaryFullPowerDegree41Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x))=c} := by

  have he : ((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x))=(boundaryRePowerRow77_15Degree41Norm x).val+(boundaryRePowerRow77_16Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree41Norm x).property (boundaryRePowerRow77_16Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree41Norm,boundaryRePowerRow77_16Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x))))=(boundaryRePowerRow77_14Degree41Norm x).val+(boundaryFullPowerDegree41Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree41Norm x).property (boundaryFullPowerDegree41Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree41Norm,boundaryFullPowerDegree41Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x))))))=(boundaryFullPowerDegree41Block11Norm x).val+(boundaryFullPowerDegree41Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block11Norm x).property (boundaryFullPowerDegree41Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block11Norm,boundaryFullPowerDegree41Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x))=c} := by

  have he : ((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x))=(boundaryRePowerRow77_18Degree41Norm x).val+(boundaryRePowerRow77_19Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree41Norm x).property (boundaryRePowerRow77_19Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree41Norm,boundaryRePowerRow77_19Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x))))=(boundaryRePowerRow77_17Degree41Norm x).val+(boundaryFullPowerDegree41Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree41Norm x).property (boundaryFullPowerDegree41Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree41Norm,boundaryFullPowerDegree41Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))=c} := by

  have he : ((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))=(boundaryRePowerRow77_21Degree41Norm x).val+(boundaryRePowerRow77_22Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree41Norm x).property (boundaryRePowerRow77_22Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree41Norm,boundaryRePowerRow77_22Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))=(boundaryRePowerRow77_20Degree41Norm x).val+(boundaryFullPowerDegree41Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree41Norm x).property (boundaryFullPowerDegree41Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree41Norm,boundaryFullPowerDegree41Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))))=(boundaryFullPowerDegree41Block16Norm x).val+(boundaryFullPowerDegree41Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block16Norm x).property (boundaryFullPowerDegree41Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block16Norm,boundaryFullPowerDegree41Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))))))=(boundaryFullPowerDegree41Block14Norm x).val+(boundaryFullPowerDegree41Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block14Norm x).property (boundaryFullPowerDegree41Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block14Norm,boundaryFullPowerDegree41Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x)))))))))+(((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x)))))))))+(((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x))))))))))=(boundaryFullPowerDegree41Block9Norm x).val+(boundaryFullPowerDegree41Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block9Norm x).property (boundaryFullPowerDegree41Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block9Norm,boundaryFullPowerDegree41Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x))=c} := by

  have he : ((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x))=(boundaryImPowerRow77_0Degree41Norm x).val+(boundaryImPowerRow77_1Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree41Norm x).property (boundaryImPowerRow77_1Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree41Norm,boundaryImPowerRow77_1Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x))=c} := by

  have he : ((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x))=(boundaryImPowerRow77_3Degree41Norm x).val+(boundaryImPowerRow77_4Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree41Norm x).property (boundaryImPowerRow77_4Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree41Norm,boundaryImPowerRow77_4Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x))))=(boundaryImPowerRow77_2Degree41Norm x).val+(boundaryFullPowerDegree41Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree41Norm x).property (boundaryFullPowerDegree41Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree41Norm,boundaryFullPowerDegree41Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x))))))=(boundaryFullPowerDegree41Block22Norm x).val+(boundaryFullPowerDegree41Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block22Norm x).property (boundaryFullPowerDegree41Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block22Norm,boundaryFullPowerDegree41Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x))=c} := by

  have he : ((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x))=(boundaryImPowerRow77_6Degree41Norm x).val+(boundaryImPowerRow77_7Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree41Norm x).property (boundaryImPowerRow77_7Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree41Norm,boundaryImPowerRow77_7Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x))))=(boundaryImPowerRow77_5Degree41Norm x).val+(boundaryFullPowerDegree41Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree41Norm x).property (boundaryFullPowerDegree41Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree41Norm,boundaryFullPowerDegree41Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))=c} := by

  have he : ((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))=(boundaryImPowerRow77_9Degree41Norm x).val+(boundaryImPowerRow77_10Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree41Norm x).property (boundaryImPowerRow77_10Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree41Norm,boundaryImPowerRow77_10Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))))=(boundaryImPowerRow77_8Degree41Norm x).val+(boundaryFullPowerDegree41Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree41Norm x).property (boundaryFullPowerDegree41Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree41Norm,boundaryFullPowerDegree41Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))))))=(boundaryFullPowerDegree41Block27Norm x).val+(boundaryFullPowerDegree41Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block27Norm x).property (boundaryFullPowerDegree41Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block27Norm,boundaryFullPowerDegree41Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x))))))))=(boundaryFullPowerDegree41Block25Norm x).val+(boundaryFullPowerDegree41Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block25Norm x).property (boundaryFullPowerDegree41Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block25Norm,boundaryFullPowerDegree41Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x))=c} := by

  have he : ((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x))=(boundaryImPowerRow77_12Degree41Norm x).val+(boundaryImPowerRow77_13Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree41Norm x).property (boundaryImPowerRow77_13Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree41Norm,boundaryImPowerRow77_13Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x))))=(boundaryImPowerRow77_11Degree41Norm x).val+(boundaryFullPowerDegree41Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree41Norm x).property (boundaryFullPowerDegree41Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree41Norm,boundaryFullPowerDegree41Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x))=c} := by

  have he : ((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x))=(boundaryImPowerRow77_15Degree41Norm x).val+(boundaryImPowerRow77_16Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree41Norm x).property (boundaryImPowerRow77_16Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree41Norm,boundaryImPowerRow77_16Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x))))=(boundaryImPowerRow77_14Degree41Norm x).val+(boundaryFullPowerDegree41Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree41Norm x).property (boundaryFullPowerDegree41Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree41Norm,boundaryFullPowerDegree41Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x))))))=(boundaryFullPowerDegree41Block33Norm x).val+(boundaryFullPowerDegree41Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block33Norm x).property (boundaryFullPowerDegree41Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block33Norm,boundaryFullPowerDegree41Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x))=c} := by

  have he : ((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x))=(boundaryImPowerRow77_18Degree41Norm x).val+(boundaryImPowerRow77_19Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree41Norm x).property (boundaryImPowerRow77_19Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree41Norm,boundaryImPowerRow77_19Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x))))=(boundaryImPowerRow77_17Degree41Norm x).val+(boundaryFullPowerDegree41Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree41Norm x).property (boundaryFullPowerDegree41Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree41Norm,boundaryFullPowerDegree41Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))=c} := by

  have he : ((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))=(boundaryImPowerRow77_21Degree41Norm x).val+(boundaryLowPowerRow77Degree41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree41Norm x).property (boundaryLowPowerRow77Degree41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree41Norm,boundaryLowPowerRow77Degree41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))=(boundaryImPowerRow77_20Degree41Norm x).val+(boundaryFullPowerDegree41Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree41Norm x).property (boundaryFullPowerDegree41Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree41Norm,boundaryFullPowerDegree41Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))=(boundaryFullPowerDegree41Block38Norm x).val+(boundaryFullPowerDegree41Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block38Norm x).property (boundaryFullPowerDegree41Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block38Norm,boundaryFullPowerDegree41Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))))=(boundaryFullPowerDegree41Block36Norm x).val+(boundaryFullPowerDegree41Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block36Norm x).property (boundaryFullPowerDegree41Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block36Norm,boundaryFullPowerDegree41Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x)))))))))+(((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x)))))))))+(((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))))))=(boundaryFullPowerDegree41Block31Norm x).val+(boundaryFullPowerDegree41Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block31Norm x).property (boundaryFullPowerDegree41Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block31Norm,boundaryFullPowerDegree41Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree41Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x)))))))))+(((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x)))))))))))+(((((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x)))))))))+(((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x)))))))))+(((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x)))))))))))+(((((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x)))))))))+(((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x))))))))))))=(boundaryFullPowerDegree41Block21Norm x).val+(boundaryFullPowerDegree41Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree41Block21Norm x).property (boundaryFullPowerDegree41Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block21Norm,boundaryFullPowerDegree41Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree41Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 41 x=c} := by

  have he0 : boundaryFullPowerRow77 41 x=((((((((((boundaryRePowerRow77_0 41 x)+(boundaryRePowerRow77_1 41 x)))+(((boundaryRePowerRow77_2 41 x)+(((boundaryRePowerRow77_3 41 x)+(boundaryRePowerRow77_4 41 x)))))))+(((((boundaryRePowerRow77_5 41 x)+(((boundaryRePowerRow77_6 41 x)+(boundaryRePowerRow77_7 41 x)))))+(((boundaryRePowerRow77_8 41 x)+(((boundaryRePowerRow77_9 41 x)+(boundaryRePowerRow77_10 41 x)))))))))+(((((((boundaryRePowerRow77_11 41 x)+(((boundaryRePowerRow77_12 41 x)+(boundaryRePowerRow77_13 41 x)))))+(((boundaryRePowerRow77_14 41 x)+(((boundaryRePowerRow77_15 41 x)+(boundaryRePowerRow77_16 41 x)))))))+(((((boundaryRePowerRow77_17 41 x)+(((boundaryRePowerRow77_18 41 x)+(boundaryRePowerRow77_19 41 x)))))+(((boundaryRePowerRow77_20 41 x)+(((boundaryRePowerRow77_21 41 x)+(boundaryRePowerRow77_22 41 x)))))))))))+(((((((((boundaryImPowerRow77_0 41 x)+(boundaryImPowerRow77_1 41 x)))+(((boundaryImPowerRow77_2 41 x)+(((boundaryImPowerRow77_3 41 x)+(boundaryImPowerRow77_4 41 x)))))))+(((((boundaryImPowerRow77_5 41 x)+(((boundaryImPowerRow77_6 41 x)+(boundaryImPowerRow77_7 41 x)))))+(((boundaryImPowerRow77_8 41 x)+(((boundaryImPowerRow77_9 41 x)+(boundaryImPowerRow77_10 41 x)))))))))+(((((((boundaryImPowerRow77_11 41 x)+(((boundaryImPowerRow77_12 41 x)+(boundaryImPowerRow77_13 41 x)))))+(((boundaryImPowerRow77_14 41 x)+(((boundaryImPowerRow77_15 41 x)+(boundaryImPowerRow77_16 41 x)))))))+(((((boundaryImPowerRow77_17 41 x)+(((boundaryImPowerRow77_18 41 x)+(boundaryImPowerRow77_19 41 x)))))+(((boundaryImPowerRow77_20 41 x)+(((boundaryImPowerRow77_21 41 x)+(boundaryLowPowerRow77 41 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree41Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree41Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
