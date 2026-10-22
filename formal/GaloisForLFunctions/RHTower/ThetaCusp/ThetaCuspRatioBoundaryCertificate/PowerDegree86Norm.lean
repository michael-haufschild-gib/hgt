import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree86Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree86Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x))=c} := by

  have he : ((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x))=(boundaryRePowerRow77_0Degree86Norm x).val+(boundaryRePowerRow77_1Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree86Norm x).property (boundaryRePowerRow77_1Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree86Norm,boundaryRePowerRow77_1Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x))=c} := by

  have he : ((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x))=(boundaryRePowerRow77_3Degree86Norm x).val+(boundaryRePowerRow77_4Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree86Norm x).property (boundaryRePowerRow77_4Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree86Norm,boundaryRePowerRow77_4Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x))))=(boundaryRePowerRow77_2Degree86Norm x).val+(boundaryFullPowerDegree86Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree86Norm x).property (boundaryFullPowerDegree86Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree86Norm,boundaryFullPowerDegree86Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x))))))=(boundaryFullPowerDegree86Block0Norm x).val+(boundaryFullPowerDegree86Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block0Norm x).property (boundaryFullPowerDegree86Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block0Norm,boundaryFullPowerDegree86Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x))=c} := by

  have he : ((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x))=(boundaryRePowerRow77_6Degree86Norm x).val+(boundaryRePowerRow77_7Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree86Norm x).property (boundaryRePowerRow77_7Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree86Norm,boundaryRePowerRow77_7Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x))))=(boundaryRePowerRow77_5Degree86Norm x).val+(boundaryFullPowerDegree86Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree86Norm x).property (boundaryFullPowerDegree86Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree86Norm,boundaryFullPowerDegree86Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))=c} := by

  have he : ((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))=(boundaryRePowerRow77_9Degree86Norm x).val+(boundaryRePowerRow77_10Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree86Norm x).property (boundaryRePowerRow77_10Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree86Norm,boundaryRePowerRow77_10Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))))=(boundaryRePowerRow77_8Degree86Norm x).val+(boundaryFullPowerDegree86Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree86Norm x).property (boundaryFullPowerDegree86Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree86Norm,boundaryFullPowerDegree86Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))))))=(boundaryFullPowerDegree86Block5Norm x).val+(boundaryFullPowerDegree86Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block5Norm x).property (boundaryFullPowerDegree86Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block5Norm,boundaryFullPowerDegree86Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x))))))))=(boundaryFullPowerDegree86Block3Norm x).val+(boundaryFullPowerDegree86Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block3Norm x).property (boundaryFullPowerDegree86Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block3Norm,boundaryFullPowerDegree86Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x))=c} := by

  have he : ((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x))=(boundaryRePowerRow77_12Degree86Norm x).val+(boundaryRePowerRow77_13Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree86Norm x).property (boundaryRePowerRow77_13Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree86Norm,boundaryRePowerRow77_13Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x))))=(boundaryRePowerRow77_11Degree86Norm x).val+(boundaryFullPowerDegree86Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree86Norm x).property (boundaryFullPowerDegree86Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree86Norm,boundaryFullPowerDegree86Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x))=c} := by

  have he : ((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x))=(boundaryRePowerRow77_15Degree86Norm x).val+(boundaryRePowerRow77_16Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree86Norm x).property (boundaryRePowerRow77_16Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree86Norm,boundaryRePowerRow77_16Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x))))=(boundaryRePowerRow77_14Degree86Norm x).val+(boundaryFullPowerDegree86Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree86Norm x).property (boundaryFullPowerDegree86Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree86Norm,boundaryFullPowerDegree86Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x))))))=(boundaryFullPowerDegree86Block11Norm x).val+(boundaryFullPowerDegree86Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block11Norm x).property (boundaryFullPowerDegree86Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block11Norm,boundaryFullPowerDegree86Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x))=c} := by

  have he : ((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x))=(boundaryRePowerRow77_18Degree86Norm x).val+(boundaryRePowerRow77_19Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree86Norm x).property (boundaryRePowerRow77_19Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree86Norm,boundaryRePowerRow77_19Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x))))=(boundaryRePowerRow77_17Degree86Norm x).val+(boundaryFullPowerDegree86Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree86Norm x).property (boundaryFullPowerDegree86Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree86Norm,boundaryFullPowerDegree86Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))=c} := by

  have he : ((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))=(boundaryRePowerRow77_21Degree86Norm x).val+(boundaryRePowerRow77_22Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree86Norm x).property (boundaryRePowerRow77_22Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree86Norm,boundaryRePowerRow77_22Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))=(boundaryRePowerRow77_20Degree86Norm x).val+(boundaryFullPowerDegree86Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree86Norm x).property (boundaryFullPowerDegree86Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree86Norm,boundaryFullPowerDegree86Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))))=(boundaryFullPowerDegree86Block16Norm x).val+(boundaryFullPowerDegree86Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block16Norm x).property (boundaryFullPowerDegree86Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block16Norm,boundaryFullPowerDegree86Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))))))=(boundaryFullPowerDegree86Block14Norm x).val+(boundaryFullPowerDegree86Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block14Norm x).property (boundaryFullPowerDegree86Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block14Norm,boundaryFullPowerDegree86Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x)))))))))+(((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x)))))))))+(((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x))))))))))=(boundaryFullPowerDegree86Block9Norm x).val+(boundaryFullPowerDegree86Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block9Norm x).property (boundaryFullPowerDegree86Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block9Norm,boundaryFullPowerDegree86Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x))=c} := by

  have he : ((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x))=(boundaryImPowerRow77_0Degree86Norm x).val+(boundaryImPowerRow77_1Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree86Norm x).property (boundaryImPowerRow77_1Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree86Norm,boundaryImPowerRow77_1Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x))=c} := by

  have he : ((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x))=(boundaryImPowerRow77_3Degree86Norm x).val+(boundaryImPowerRow77_4Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree86Norm x).property (boundaryImPowerRow77_4Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree86Norm,boundaryImPowerRow77_4Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x))))=(boundaryImPowerRow77_2Degree86Norm x).val+(boundaryFullPowerDegree86Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree86Norm x).property (boundaryFullPowerDegree86Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree86Norm,boundaryFullPowerDegree86Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x))))))=(boundaryFullPowerDegree86Block22Norm x).val+(boundaryFullPowerDegree86Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block22Norm x).property (boundaryFullPowerDegree86Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block22Norm,boundaryFullPowerDegree86Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x))=c} := by

  have he : ((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x))=(boundaryImPowerRow77_6Degree86Norm x).val+(boundaryImPowerRow77_7Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree86Norm x).property (boundaryImPowerRow77_7Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree86Norm,boundaryImPowerRow77_7Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x))))=(boundaryImPowerRow77_5Degree86Norm x).val+(boundaryFullPowerDegree86Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree86Norm x).property (boundaryFullPowerDegree86Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree86Norm,boundaryFullPowerDegree86Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))=c} := by

  have he : ((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))=(boundaryImPowerRow77_9Degree86Norm x).val+(boundaryImPowerRow77_10Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree86Norm x).property (boundaryImPowerRow77_10Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree86Norm,boundaryImPowerRow77_10Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))))=(boundaryImPowerRow77_8Degree86Norm x).val+(boundaryFullPowerDegree86Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree86Norm x).property (boundaryFullPowerDegree86Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree86Norm,boundaryFullPowerDegree86Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))))))=(boundaryFullPowerDegree86Block27Norm x).val+(boundaryFullPowerDegree86Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block27Norm x).property (boundaryFullPowerDegree86Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block27Norm,boundaryFullPowerDegree86Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x))))))))=(boundaryFullPowerDegree86Block25Norm x).val+(boundaryFullPowerDegree86Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block25Norm x).property (boundaryFullPowerDegree86Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block25Norm,boundaryFullPowerDegree86Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x))=c} := by

  have he : ((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x))=(boundaryImPowerRow77_12Degree86Norm x).val+(boundaryImPowerRow77_13Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree86Norm x).property (boundaryImPowerRow77_13Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree86Norm,boundaryImPowerRow77_13Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x))))=(boundaryImPowerRow77_11Degree86Norm x).val+(boundaryFullPowerDegree86Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree86Norm x).property (boundaryFullPowerDegree86Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree86Norm,boundaryFullPowerDegree86Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x))=c} := by

  have he : ((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x))=(boundaryImPowerRow77_15Degree86Norm x).val+(boundaryImPowerRow77_16Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree86Norm x).property (boundaryImPowerRow77_16Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree86Norm,boundaryImPowerRow77_16Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x))))=(boundaryImPowerRow77_14Degree86Norm x).val+(boundaryFullPowerDegree86Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree86Norm x).property (boundaryFullPowerDegree86Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree86Norm,boundaryFullPowerDegree86Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x))))))=(boundaryFullPowerDegree86Block33Norm x).val+(boundaryFullPowerDegree86Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block33Norm x).property (boundaryFullPowerDegree86Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block33Norm,boundaryFullPowerDegree86Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x))=c} := by

  have he : ((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x))=(boundaryImPowerRow77_18Degree86Norm x).val+(boundaryImPowerRow77_19Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree86Norm x).property (boundaryImPowerRow77_19Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree86Norm,boundaryImPowerRow77_19Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x))))=(boundaryImPowerRow77_17Degree86Norm x).val+(boundaryFullPowerDegree86Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree86Norm x).property (boundaryFullPowerDegree86Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree86Norm,boundaryFullPowerDegree86Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))=c} := by

  have he : ((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))=(boundaryImPowerRow77_21Degree86Norm x).val+(boundaryLowPowerRow77Degree86Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree86Norm x).property (boundaryLowPowerRow77Degree86Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree86Norm,boundaryLowPowerRow77Degree86Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))=(boundaryImPowerRow77_20Degree86Norm x).val+(boundaryFullPowerDegree86Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree86Norm x).property (boundaryFullPowerDegree86Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree86Norm,boundaryFullPowerDegree86Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))=(boundaryFullPowerDegree86Block38Norm x).val+(boundaryFullPowerDegree86Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block38Norm x).property (boundaryFullPowerDegree86Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block38Norm,boundaryFullPowerDegree86Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))))=(boundaryFullPowerDegree86Block36Norm x).val+(boundaryFullPowerDegree86Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block36Norm x).property (boundaryFullPowerDegree86Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block36Norm,boundaryFullPowerDegree86Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x)))))))))+(((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x)))))))))+(((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))))))=(boundaryFullPowerDegree86Block31Norm x).val+(boundaryFullPowerDegree86Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block31Norm x).property (boundaryFullPowerDegree86Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block31Norm,boundaryFullPowerDegree86Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree86Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x)))))))))+(((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x)))))))))))+(((((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x)))))))))+(((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x)))))))))+(((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x)))))))))))+(((((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x)))))))))+(((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x))))))))))))=(boundaryFullPowerDegree86Block21Norm x).val+(boundaryFullPowerDegree86Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree86Block21Norm x).property (boundaryFullPowerDegree86Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block21Norm,boundaryFullPowerDegree86Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree86Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 86 x=c} := by

  have he0 : boundaryFullPowerRow77 86 x=((((((((((boundaryRePowerRow77_0 86 x)+(boundaryRePowerRow77_1 86 x)))+(((boundaryRePowerRow77_2 86 x)+(((boundaryRePowerRow77_3 86 x)+(boundaryRePowerRow77_4 86 x)))))))+(((((boundaryRePowerRow77_5 86 x)+(((boundaryRePowerRow77_6 86 x)+(boundaryRePowerRow77_7 86 x)))))+(((boundaryRePowerRow77_8 86 x)+(((boundaryRePowerRow77_9 86 x)+(boundaryRePowerRow77_10 86 x)))))))))+(((((((boundaryRePowerRow77_11 86 x)+(((boundaryRePowerRow77_12 86 x)+(boundaryRePowerRow77_13 86 x)))))+(((boundaryRePowerRow77_14 86 x)+(((boundaryRePowerRow77_15 86 x)+(boundaryRePowerRow77_16 86 x)))))))+(((((boundaryRePowerRow77_17 86 x)+(((boundaryRePowerRow77_18 86 x)+(boundaryRePowerRow77_19 86 x)))))+(((boundaryRePowerRow77_20 86 x)+(((boundaryRePowerRow77_21 86 x)+(boundaryRePowerRow77_22 86 x)))))))))))+(((((((((boundaryImPowerRow77_0 86 x)+(boundaryImPowerRow77_1 86 x)))+(((boundaryImPowerRow77_2 86 x)+(((boundaryImPowerRow77_3 86 x)+(boundaryImPowerRow77_4 86 x)))))))+(((((boundaryImPowerRow77_5 86 x)+(((boundaryImPowerRow77_6 86 x)+(boundaryImPowerRow77_7 86 x)))))+(((boundaryImPowerRow77_8 86 x)+(((boundaryImPowerRow77_9 86 x)+(boundaryImPowerRow77_10 86 x)))))))))+(((((((boundaryImPowerRow77_11 86 x)+(((boundaryImPowerRow77_12 86 x)+(boundaryImPowerRow77_13 86 x)))))+(((boundaryImPowerRow77_14 86 x)+(((boundaryImPowerRow77_15 86 x)+(boundaryImPowerRow77_16 86 x)))))))+(((((boundaryImPowerRow77_17 86 x)+(((boundaryImPowerRow77_18 86 x)+(boundaryImPowerRow77_19 86 x)))))+(((boundaryImPowerRow77_20 86 x)+(((boundaryImPowerRow77_21 86 x)+(boundaryLowPowerRow77 86 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree86Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree86Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
