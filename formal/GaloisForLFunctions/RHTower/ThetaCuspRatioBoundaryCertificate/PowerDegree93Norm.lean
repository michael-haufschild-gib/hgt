import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree93Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree93Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x))=c} := by

  have he : ((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x))=(boundaryRePowerRow77_0Degree93Norm x).val+(boundaryRePowerRow77_1Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree93Norm x).property (boundaryRePowerRow77_1Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree93Norm,boundaryRePowerRow77_1Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x))=c} := by

  have he : ((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x))=(boundaryRePowerRow77_3Degree93Norm x).val+(boundaryRePowerRow77_4Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree93Norm x).property (boundaryRePowerRow77_4Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree93Norm,boundaryRePowerRow77_4Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x))))=(boundaryRePowerRow77_2Degree93Norm x).val+(boundaryFullPowerDegree93Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree93Norm x).property (boundaryFullPowerDegree93Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree93Norm,boundaryFullPowerDegree93Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x))))))=(boundaryFullPowerDegree93Block0Norm x).val+(boundaryFullPowerDegree93Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block0Norm x).property (boundaryFullPowerDegree93Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block0Norm,boundaryFullPowerDegree93Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x))=c} := by

  have he : ((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x))=(boundaryRePowerRow77_6Degree93Norm x).val+(boundaryRePowerRow77_7Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree93Norm x).property (boundaryRePowerRow77_7Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree93Norm,boundaryRePowerRow77_7Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x))))=(boundaryRePowerRow77_5Degree93Norm x).val+(boundaryFullPowerDegree93Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree93Norm x).property (boundaryFullPowerDegree93Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree93Norm,boundaryFullPowerDegree93Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))=c} := by

  have he : ((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))=(boundaryRePowerRow77_9Degree93Norm x).val+(boundaryRePowerRow77_10Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree93Norm x).property (boundaryRePowerRow77_10Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree93Norm,boundaryRePowerRow77_10Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))))=(boundaryRePowerRow77_8Degree93Norm x).val+(boundaryFullPowerDegree93Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree93Norm x).property (boundaryFullPowerDegree93Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree93Norm,boundaryFullPowerDegree93Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))))))=(boundaryFullPowerDegree93Block5Norm x).val+(boundaryFullPowerDegree93Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block5Norm x).property (boundaryFullPowerDegree93Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block5Norm,boundaryFullPowerDegree93Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x))))))))=(boundaryFullPowerDegree93Block3Norm x).val+(boundaryFullPowerDegree93Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block3Norm x).property (boundaryFullPowerDegree93Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block3Norm,boundaryFullPowerDegree93Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x))=c} := by

  have he : ((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x))=(boundaryRePowerRow77_12Degree93Norm x).val+(boundaryRePowerRow77_13Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree93Norm x).property (boundaryRePowerRow77_13Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree93Norm,boundaryRePowerRow77_13Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x))))=(boundaryRePowerRow77_11Degree93Norm x).val+(boundaryFullPowerDegree93Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree93Norm x).property (boundaryFullPowerDegree93Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree93Norm,boundaryFullPowerDegree93Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x))=c} := by

  have he : ((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x))=(boundaryRePowerRow77_15Degree93Norm x).val+(boundaryRePowerRow77_16Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree93Norm x).property (boundaryRePowerRow77_16Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree93Norm,boundaryRePowerRow77_16Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x))))=(boundaryRePowerRow77_14Degree93Norm x).val+(boundaryFullPowerDegree93Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree93Norm x).property (boundaryFullPowerDegree93Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree93Norm,boundaryFullPowerDegree93Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x))))))=(boundaryFullPowerDegree93Block11Norm x).val+(boundaryFullPowerDegree93Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block11Norm x).property (boundaryFullPowerDegree93Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block11Norm,boundaryFullPowerDegree93Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x))=c} := by

  have he : ((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x))=(boundaryRePowerRow77_18Degree93Norm x).val+(boundaryRePowerRow77_19Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree93Norm x).property (boundaryRePowerRow77_19Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree93Norm,boundaryRePowerRow77_19Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x))))=(boundaryRePowerRow77_17Degree93Norm x).val+(boundaryFullPowerDegree93Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree93Norm x).property (boundaryFullPowerDegree93Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree93Norm,boundaryFullPowerDegree93Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))=c} := by

  have he : ((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))=(boundaryRePowerRow77_21Degree93Norm x).val+(boundaryRePowerRow77_22Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree93Norm x).property (boundaryRePowerRow77_22Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree93Norm,boundaryRePowerRow77_22Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))=(boundaryRePowerRow77_20Degree93Norm x).val+(boundaryFullPowerDegree93Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree93Norm x).property (boundaryFullPowerDegree93Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree93Norm,boundaryFullPowerDegree93Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))))=(boundaryFullPowerDegree93Block16Norm x).val+(boundaryFullPowerDegree93Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block16Norm x).property (boundaryFullPowerDegree93Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block16Norm,boundaryFullPowerDegree93Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))))))=(boundaryFullPowerDegree93Block14Norm x).val+(boundaryFullPowerDegree93Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block14Norm x).property (boundaryFullPowerDegree93Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block14Norm,boundaryFullPowerDegree93Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x)))))))))+(((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x)))))))))+(((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x))))))))))=(boundaryFullPowerDegree93Block9Norm x).val+(boundaryFullPowerDegree93Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block9Norm x).property (boundaryFullPowerDegree93Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block9Norm,boundaryFullPowerDegree93Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x))=c} := by

  have he : ((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x))=(boundaryImPowerRow77_0Degree93Norm x).val+(boundaryImPowerRow77_1Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree93Norm x).property (boundaryImPowerRow77_1Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree93Norm,boundaryImPowerRow77_1Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x))=c} := by

  have he : ((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x))=(boundaryImPowerRow77_3Degree93Norm x).val+(boundaryImPowerRow77_4Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree93Norm x).property (boundaryImPowerRow77_4Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree93Norm,boundaryImPowerRow77_4Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x))))=(boundaryImPowerRow77_2Degree93Norm x).val+(boundaryFullPowerDegree93Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree93Norm x).property (boundaryFullPowerDegree93Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree93Norm,boundaryFullPowerDegree93Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x))))))=(boundaryFullPowerDegree93Block22Norm x).val+(boundaryFullPowerDegree93Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block22Norm x).property (boundaryFullPowerDegree93Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block22Norm,boundaryFullPowerDegree93Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x))=c} := by

  have he : ((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x))=(boundaryImPowerRow77_6Degree93Norm x).val+(boundaryImPowerRow77_7Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree93Norm x).property (boundaryImPowerRow77_7Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree93Norm,boundaryImPowerRow77_7Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x))))=(boundaryImPowerRow77_5Degree93Norm x).val+(boundaryFullPowerDegree93Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree93Norm x).property (boundaryFullPowerDegree93Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree93Norm,boundaryFullPowerDegree93Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))=c} := by

  have he : ((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))=(boundaryImPowerRow77_9Degree93Norm x).val+(boundaryImPowerRow77_10Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree93Norm x).property (boundaryImPowerRow77_10Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree93Norm,boundaryImPowerRow77_10Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))))=(boundaryImPowerRow77_8Degree93Norm x).val+(boundaryFullPowerDegree93Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree93Norm x).property (boundaryFullPowerDegree93Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree93Norm,boundaryFullPowerDegree93Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))))))=(boundaryFullPowerDegree93Block27Norm x).val+(boundaryFullPowerDegree93Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block27Norm x).property (boundaryFullPowerDegree93Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block27Norm,boundaryFullPowerDegree93Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x))))))))=(boundaryFullPowerDegree93Block25Norm x).val+(boundaryFullPowerDegree93Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block25Norm x).property (boundaryFullPowerDegree93Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block25Norm,boundaryFullPowerDegree93Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x))=c} := by

  have he : ((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x))=(boundaryImPowerRow77_12Degree93Norm x).val+(boundaryImPowerRow77_13Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree93Norm x).property (boundaryImPowerRow77_13Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree93Norm,boundaryImPowerRow77_13Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x))))=(boundaryImPowerRow77_11Degree93Norm x).val+(boundaryFullPowerDegree93Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree93Norm x).property (boundaryFullPowerDegree93Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree93Norm,boundaryFullPowerDegree93Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x))=c} := by

  have he : ((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x))=(boundaryImPowerRow77_15Degree93Norm x).val+(boundaryImPowerRow77_16Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree93Norm x).property (boundaryImPowerRow77_16Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree93Norm,boundaryImPowerRow77_16Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x))))=(boundaryImPowerRow77_14Degree93Norm x).val+(boundaryFullPowerDegree93Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree93Norm x).property (boundaryFullPowerDegree93Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree93Norm,boundaryFullPowerDegree93Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x))))))=(boundaryFullPowerDegree93Block33Norm x).val+(boundaryFullPowerDegree93Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block33Norm x).property (boundaryFullPowerDegree93Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block33Norm,boundaryFullPowerDegree93Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x))=c} := by

  have he : ((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x))=(boundaryImPowerRow77_18Degree93Norm x).val+(boundaryImPowerRow77_19Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree93Norm x).property (boundaryImPowerRow77_19Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree93Norm,boundaryImPowerRow77_19Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x))))=(boundaryImPowerRow77_17Degree93Norm x).val+(boundaryFullPowerDegree93Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree93Norm x).property (boundaryFullPowerDegree93Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree93Norm,boundaryFullPowerDegree93Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))=c} := by

  have he : ((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))=(boundaryImPowerRow77_21Degree93Norm x).val+(boundaryLowPowerRow77Degree93Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree93Norm x).property (boundaryLowPowerRow77Degree93Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree93Norm,boundaryLowPowerRow77Degree93Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))=(boundaryImPowerRow77_20Degree93Norm x).val+(boundaryFullPowerDegree93Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree93Norm x).property (boundaryFullPowerDegree93Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree93Norm,boundaryFullPowerDegree93Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))=(boundaryFullPowerDegree93Block38Norm x).val+(boundaryFullPowerDegree93Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block38Norm x).property (boundaryFullPowerDegree93Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block38Norm,boundaryFullPowerDegree93Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))))=(boundaryFullPowerDegree93Block36Norm x).val+(boundaryFullPowerDegree93Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block36Norm x).property (boundaryFullPowerDegree93Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block36Norm,boundaryFullPowerDegree93Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x)))))))))+(((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x)))))))))+(((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))))))=(boundaryFullPowerDegree93Block31Norm x).val+(boundaryFullPowerDegree93Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block31Norm x).property (boundaryFullPowerDegree93Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block31Norm,boundaryFullPowerDegree93Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree93Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x)))))))))+(((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x)))))))))))+(((((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x)))))))))+(((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x)))))))))+(((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x)))))))))))+(((((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x)))))))))+(((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x))))))))))))=(boundaryFullPowerDegree93Block21Norm x).val+(boundaryFullPowerDegree93Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree93Block21Norm x).property (boundaryFullPowerDegree93Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block21Norm,boundaryFullPowerDegree93Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree93Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 93 x=c} := by

  have he0 : boundaryFullPowerRow77 93 x=((((((((((boundaryRePowerRow77_0 93 x)+(boundaryRePowerRow77_1 93 x)))+(((boundaryRePowerRow77_2 93 x)+(((boundaryRePowerRow77_3 93 x)+(boundaryRePowerRow77_4 93 x)))))))+(((((boundaryRePowerRow77_5 93 x)+(((boundaryRePowerRow77_6 93 x)+(boundaryRePowerRow77_7 93 x)))))+(((boundaryRePowerRow77_8 93 x)+(((boundaryRePowerRow77_9 93 x)+(boundaryRePowerRow77_10 93 x)))))))))+(((((((boundaryRePowerRow77_11 93 x)+(((boundaryRePowerRow77_12 93 x)+(boundaryRePowerRow77_13 93 x)))))+(((boundaryRePowerRow77_14 93 x)+(((boundaryRePowerRow77_15 93 x)+(boundaryRePowerRow77_16 93 x)))))))+(((((boundaryRePowerRow77_17 93 x)+(((boundaryRePowerRow77_18 93 x)+(boundaryRePowerRow77_19 93 x)))))+(((boundaryRePowerRow77_20 93 x)+(((boundaryRePowerRow77_21 93 x)+(boundaryRePowerRow77_22 93 x)))))))))))+(((((((((boundaryImPowerRow77_0 93 x)+(boundaryImPowerRow77_1 93 x)))+(((boundaryImPowerRow77_2 93 x)+(((boundaryImPowerRow77_3 93 x)+(boundaryImPowerRow77_4 93 x)))))))+(((((boundaryImPowerRow77_5 93 x)+(((boundaryImPowerRow77_6 93 x)+(boundaryImPowerRow77_7 93 x)))))+(((boundaryImPowerRow77_8 93 x)+(((boundaryImPowerRow77_9 93 x)+(boundaryImPowerRow77_10 93 x)))))))))+(((((((boundaryImPowerRow77_11 93 x)+(((boundaryImPowerRow77_12 93 x)+(boundaryImPowerRow77_13 93 x)))))+(((boundaryImPowerRow77_14 93 x)+(((boundaryImPowerRow77_15 93 x)+(boundaryImPowerRow77_16 93 x)))))))+(((((boundaryImPowerRow77_17 93 x)+(((boundaryImPowerRow77_18 93 x)+(boundaryImPowerRow77_19 93 x)))))+(((boundaryImPowerRow77_20 93 x)+(((boundaryImPowerRow77_21 93 x)+(boundaryLowPowerRow77 93 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree93Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree93Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
