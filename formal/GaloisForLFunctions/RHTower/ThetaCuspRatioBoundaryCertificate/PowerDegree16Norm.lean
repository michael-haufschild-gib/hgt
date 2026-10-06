import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree16Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree16Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x))=c} := by

  have he : ((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x))=(boundaryRePowerRow77_0Degree16Norm x).val+(boundaryRePowerRow77_1Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree16Norm x).property (boundaryRePowerRow77_1Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree16Norm,boundaryRePowerRow77_1Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x))=c} := by

  have he : ((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x))=(boundaryRePowerRow77_3Degree16Norm x).val+(boundaryRePowerRow77_4Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree16Norm x).property (boundaryRePowerRow77_4Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree16Norm,boundaryRePowerRow77_4Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x))))=(boundaryRePowerRow77_2Degree16Norm x).val+(boundaryFullPowerDegree16Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree16Norm x).property (boundaryFullPowerDegree16Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree16Norm,boundaryFullPowerDegree16Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x))))))=(boundaryFullPowerDegree16Block0Norm x).val+(boundaryFullPowerDegree16Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block0Norm x).property (boundaryFullPowerDegree16Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block0Norm,boundaryFullPowerDegree16Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x))=c} := by

  have he : ((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x))=(boundaryRePowerRow77_6Degree16Norm x).val+(boundaryRePowerRow77_7Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree16Norm x).property (boundaryRePowerRow77_7Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree16Norm,boundaryRePowerRow77_7Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x))))=(boundaryRePowerRow77_5Degree16Norm x).val+(boundaryFullPowerDegree16Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree16Norm x).property (boundaryFullPowerDegree16Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree16Norm,boundaryFullPowerDegree16Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))=c} := by

  have he : ((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))=(boundaryRePowerRow77_9Degree16Norm x).val+(boundaryRePowerRow77_10Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree16Norm x).property (boundaryRePowerRow77_10Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree16Norm,boundaryRePowerRow77_10Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))))=(boundaryRePowerRow77_8Degree16Norm x).val+(boundaryFullPowerDegree16Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree16Norm x).property (boundaryFullPowerDegree16Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree16Norm,boundaryFullPowerDegree16Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))))))=(boundaryFullPowerDegree16Block5Norm x).val+(boundaryFullPowerDegree16Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block5Norm x).property (boundaryFullPowerDegree16Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block5Norm,boundaryFullPowerDegree16Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x))))))))=(boundaryFullPowerDegree16Block3Norm x).val+(boundaryFullPowerDegree16Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block3Norm x).property (boundaryFullPowerDegree16Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block3Norm,boundaryFullPowerDegree16Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x))=c} := by

  have he : ((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x))=(boundaryRePowerRow77_12Degree16Norm x).val+(boundaryRePowerRow77_13Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree16Norm x).property (boundaryRePowerRow77_13Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree16Norm,boundaryRePowerRow77_13Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x))))=(boundaryRePowerRow77_11Degree16Norm x).val+(boundaryFullPowerDegree16Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree16Norm x).property (boundaryFullPowerDegree16Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree16Norm,boundaryFullPowerDegree16Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x))=c} := by

  have he : ((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x))=(boundaryRePowerRow77_15Degree16Norm x).val+(boundaryRePowerRow77_16Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree16Norm x).property (boundaryRePowerRow77_16Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree16Norm,boundaryRePowerRow77_16Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x))))=(boundaryRePowerRow77_14Degree16Norm x).val+(boundaryFullPowerDegree16Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree16Norm x).property (boundaryFullPowerDegree16Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree16Norm,boundaryFullPowerDegree16Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x))))))=(boundaryFullPowerDegree16Block11Norm x).val+(boundaryFullPowerDegree16Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block11Norm x).property (boundaryFullPowerDegree16Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block11Norm,boundaryFullPowerDegree16Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x))=c} := by

  have he : ((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x))=(boundaryRePowerRow77_18Degree16Norm x).val+(boundaryRePowerRow77_19Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree16Norm x).property (boundaryRePowerRow77_19Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree16Norm,boundaryRePowerRow77_19Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x))))=(boundaryRePowerRow77_17Degree16Norm x).val+(boundaryFullPowerDegree16Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree16Norm x).property (boundaryFullPowerDegree16Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree16Norm,boundaryFullPowerDegree16Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))=c} := by

  have he : ((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))=(boundaryRePowerRow77_21Degree16Norm x).val+(boundaryRePowerRow77_22Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree16Norm x).property (boundaryRePowerRow77_22Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree16Norm,boundaryRePowerRow77_22Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))=(boundaryRePowerRow77_20Degree16Norm x).val+(boundaryFullPowerDegree16Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree16Norm x).property (boundaryFullPowerDegree16Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree16Norm,boundaryFullPowerDegree16Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))))=(boundaryFullPowerDegree16Block16Norm x).val+(boundaryFullPowerDegree16Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block16Norm x).property (boundaryFullPowerDegree16Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block16Norm,boundaryFullPowerDegree16Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))))))=(boundaryFullPowerDegree16Block14Norm x).val+(boundaryFullPowerDegree16Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block14Norm x).property (boundaryFullPowerDegree16Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block14Norm,boundaryFullPowerDegree16Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x)))))))))+(((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x)))))))))+(((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x))))))))))=(boundaryFullPowerDegree16Block9Norm x).val+(boundaryFullPowerDegree16Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block9Norm x).property (boundaryFullPowerDegree16Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block9Norm,boundaryFullPowerDegree16Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x))=c} := by

  have he : ((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x))=(boundaryImPowerRow77_0Degree16Norm x).val+(boundaryImPowerRow77_1Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree16Norm x).property (boundaryImPowerRow77_1Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree16Norm,boundaryImPowerRow77_1Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x))=c} := by

  have he : ((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x))=(boundaryImPowerRow77_3Degree16Norm x).val+(boundaryImPowerRow77_4Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree16Norm x).property (boundaryImPowerRow77_4Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree16Norm,boundaryImPowerRow77_4Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x))))=(boundaryImPowerRow77_2Degree16Norm x).val+(boundaryFullPowerDegree16Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree16Norm x).property (boundaryFullPowerDegree16Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree16Norm,boundaryFullPowerDegree16Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x))))))=(boundaryFullPowerDegree16Block22Norm x).val+(boundaryFullPowerDegree16Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block22Norm x).property (boundaryFullPowerDegree16Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block22Norm,boundaryFullPowerDegree16Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x))=c} := by

  have he : ((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x))=(boundaryImPowerRow77_6Degree16Norm x).val+(boundaryImPowerRow77_7Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree16Norm x).property (boundaryImPowerRow77_7Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree16Norm,boundaryImPowerRow77_7Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x))))=(boundaryImPowerRow77_5Degree16Norm x).val+(boundaryFullPowerDegree16Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree16Norm x).property (boundaryFullPowerDegree16Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree16Norm,boundaryFullPowerDegree16Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))=c} := by

  have he : ((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))=(boundaryImPowerRow77_9Degree16Norm x).val+(boundaryImPowerRow77_10Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree16Norm x).property (boundaryImPowerRow77_10Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree16Norm,boundaryImPowerRow77_10Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))))=(boundaryImPowerRow77_8Degree16Norm x).val+(boundaryFullPowerDegree16Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree16Norm x).property (boundaryFullPowerDegree16Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree16Norm,boundaryFullPowerDegree16Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))))))=(boundaryFullPowerDegree16Block27Norm x).val+(boundaryFullPowerDegree16Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block27Norm x).property (boundaryFullPowerDegree16Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block27Norm,boundaryFullPowerDegree16Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x))))))))=(boundaryFullPowerDegree16Block25Norm x).val+(boundaryFullPowerDegree16Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block25Norm x).property (boundaryFullPowerDegree16Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block25Norm,boundaryFullPowerDegree16Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x))=c} := by

  have he : ((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x))=(boundaryImPowerRow77_12Degree16Norm x).val+(boundaryImPowerRow77_13Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree16Norm x).property (boundaryImPowerRow77_13Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree16Norm,boundaryImPowerRow77_13Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x))))=(boundaryImPowerRow77_11Degree16Norm x).val+(boundaryFullPowerDegree16Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree16Norm x).property (boundaryFullPowerDegree16Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree16Norm,boundaryFullPowerDegree16Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x))=c} := by

  have he : ((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x))=(boundaryImPowerRow77_15Degree16Norm x).val+(boundaryImPowerRow77_16Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree16Norm x).property (boundaryImPowerRow77_16Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree16Norm,boundaryImPowerRow77_16Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x))))=(boundaryImPowerRow77_14Degree16Norm x).val+(boundaryFullPowerDegree16Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree16Norm x).property (boundaryFullPowerDegree16Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree16Norm,boundaryFullPowerDegree16Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x))))))=(boundaryFullPowerDegree16Block33Norm x).val+(boundaryFullPowerDegree16Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block33Norm x).property (boundaryFullPowerDegree16Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block33Norm,boundaryFullPowerDegree16Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x))=c} := by

  have he : ((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x))=(boundaryImPowerRow77_18Degree16Norm x).val+(boundaryImPowerRow77_19Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree16Norm x).property (boundaryImPowerRow77_19Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree16Norm,boundaryImPowerRow77_19Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x))))=(boundaryImPowerRow77_17Degree16Norm x).val+(boundaryFullPowerDegree16Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree16Norm x).property (boundaryFullPowerDegree16Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree16Norm,boundaryFullPowerDegree16Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))=c} := by

  have he : ((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))=(boundaryImPowerRow77_21Degree16Norm x).val+(boundaryLowPowerRow77Degree16Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree16Norm x).property (boundaryLowPowerRow77Degree16Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree16Norm,boundaryLowPowerRow77Degree16Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))=(boundaryImPowerRow77_20Degree16Norm x).val+(boundaryFullPowerDegree16Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree16Norm x).property (boundaryFullPowerDegree16Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree16Norm,boundaryFullPowerDegree16Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))=(boundaryFullPowerDegree16Block38Norm x).val+(boundaryFullPowerDegree16Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block38Norm x).property (boundaryFullPowerDegree16Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block38Norm,boundaryFullPowerDegree16Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))))=(boundaryFullPowerDegree16Block36Norm x).val+(boundaryFullPowerDegree16Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block36Norm x).property (boundaryFullPowerDegree16Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block36Norm,boundaryFullPowerDegree16Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x)))))))))+(((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x)))))))))+(((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))))))=(boundaryFullPowerDegree16Block31Norm x).val+(boundaryFullPowerDegree16Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block31Norm x).property (boundaryFullPowerDegree16Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block31Norm,boundaryFullPowerDegree16Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree16Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x)))))))))+(((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x)))))))))))+(((((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x)))))))))+(((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x)))))))))+(((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x)))))))))))+(((((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x)))))))))+(((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x))))))))))))=(boundaryFullPowerDegree16Block21Norm x).val+(boundaryFullPowerDegree16Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree16Block21Norm x).property (boundaryFullPowerDegree16Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block21Norm,boundaryFullPowerDegree16Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree16Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 16 x=c} := by

  have he0 : boundaryFullPowerRow77 16 x=((((((((((boundaryRePowerRow77_0 16 x)+(boundaryRePowerRow77_1 16 x)))+(((boundaryRePowerRow77_2 16 x)+(((boundaryRePowerRow77_3 16 x)+(boundaryRePowerRow77_4 16 x)))))))+(((((boundaryRePowerRow77_5 16 x)+(((boundaryRePowerRow77_6 16 x)+(boundaryRePowerRow77_7 16 x)))))+(((boundaryRePowerRow77_8 16 x)+(((boundaryRePowerRow77_9 16 x)+(boundaryRePowerRow77_10 16 x)))))))))+(((((((boundaryRePowerRow77_11 16 x)+(((boundaryRePowerRow77_12 16 x)+(boundaryRePowerRow77_13 16 x)))))+(((boundaryRePowerRow77_14 16 x)+(((boundaryRePowerRow77_15 16 x)+(boundaryRePowerRow77_16 16 x)))))))+(((((boundaryRePowerRow77_17 16 x)+(((boundaryRePowerRow77_18 16 x)+(boundaryRePowerRow77_19 16 x)))))+(((boundaryRePowerRow77_20 16 x)+(((boundaryRePowerRow77_21 16 x)+(boundaryRePowerRow77_22 16 x)))))))))))+(((((((((boundaryImPowerRow77_0 16 x)+(boundaryImPowerRow77_1 16 x)))+(((boundaryImPowerRow77_2 16 x)+(((boundaryImPowerRow77_3 16 x)+(boundaryImPowerRow77_4 16 x)))))))+(((((boundaryImPowerRow77_5 16 x)+(((boundaryImPowerRow77_6 16 x)+(boundaryImPowerRow77_7 16 x)))))+(((boundaryImPowerRow77_8 16 x)+(((boundaryImPowerRow77_9 16 x)+(boundaryImPowerRow77_10 16 x)))))))))+(((((((boundaryImPowerRow77_11 16 x)+(((boundaryImPowerRow77_12 16 x)+(boundaryImPowerRow77_13 16 x)))))+(((boundaryImPowerRow77_14 16 x)+(((boundaryImPowerRow77_15 16 x)+(boundaryImPowerRow77_16 16 x)))))))+(((((boundaryImPowerRow77_17 16 x)+(((boundaryImPowerRow77_18 16 x)+(boundaryImPowerRow77_19 16 x)))))+(((boundaryImPowerRow77_20 16 x)+(((boundaryImPowerRow77_21 16 x)+(boundaryLowPowerRow77 16 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree16Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree16Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
