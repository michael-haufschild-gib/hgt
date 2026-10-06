import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree51Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree51Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x))=c} := by

  have he : ((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x))=(boundaryRePowerRow77_0Degree51Norm x).val+(boundaryRePowerRow77_1Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree51Norm x).property (boundaryRePowerRow77_1Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree51Norm,boundaryRePowerRow77_1Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x))=c} := by

  have he : ((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x))=(boundaryRePowerRow77_3Degree51Norm x).val+(boundaryRePowerRow77_4Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree51Norm x).property (boundaryRePowerRow77_4Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree51Norm,boundaryRePowerRow77_4Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x))))=(boundaryRePowerRow77_2Degree51Norm x).val+(boundaryFullPowerDegree51Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree51Norm x).property (boundaryFullPowerDegree51Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree51Norm,boundaryFullPowerDegree51Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x))))))=(boundaryFullPowerDegree51Block0Norm x).val+(boundaryFullPowerDegree51Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block0Norm x).property (boundaryFullPowerDegree51Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block0Norm,boundaryFullPowerDegree51Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x))=c} := by

  have he : ((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x))=(boundaryRePowerRow77_6Degree51Norm x).val+(boundaryRePowerRow77_7Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree51Norm x).property (boundaryRePowerRow77_7Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree51Norm,boundaryRePowerRow77_7Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x))))=(boundaryRePowerRow77_5Degree51Norm x).val+(boundaryFullPowerDegree51Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree51Norm x).property (boundaryFullPowerDegree51Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree51Norm,boundaryFullPowerDegree51Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))=c} := by

  have he : ((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))=(boundaryRePowerRow77_9Degree51Norm x).val+(boundaryRePowerRow77_10Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree51Norm x).property (boundaryRePowerRow77_10Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree51Norm,boundaryRePowerRow77_10Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))))=(boundaryRePowerRow77_8Degree51Norm x).val+(boundaryFullPowerDegree51Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree51Norm x).property (boundaryFullPowerDegree51Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree51Norm,boundaryFullPowerDegree51Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))))))=(boundaryFullPowerDegree51Block5Norm x).val+(boundaryFullPowerDegree51Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block5Norm x).property (boundaryFullPowerDegree51Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block5Norm,boundaryFullPowerDegree51Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x))))))))=(boundaryFullPowerDegree51Block3Norm x).val+(boundaryFullPowerDegree51Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block3Norm x).property (boundaryFullPowerDegree51Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block3Norm,boundaryFullPowerDegree51Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x))=c} := by

  have he : ((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x))=(boundaryRePowerRow77_12Degree51Norm x).val+(boundaryRePowerRow77_13Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree51Norm x).property (boundaryRePowerRow77_13Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree51Norm,boundaryRePowerRow77_13Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x))))=(boundaryRePowerRow77_11Degree51Norm x).val+(boundaryFullPowerDegree51Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree51Norm x).property (boundaryFullPowerDegree51Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree51Norm,boundaryFullPowerDegree51Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x))=c} := by

  have he : ((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x))=(boundaryRePowerRow77_15Degree51Norm x).val+(boundaryRePowerRow77_16Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree51Norm x).property (boundaryRePowerRow77_16Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree51Norm,boundaryRePowerRow77_16Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x))))=(boundaryRePowerRow77_14Degree51Norm x).val+(boundaryFullPowerDegree51Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree51Norm x).property (boundaryFullPowerDegree51Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree51Norm,boundaryFullPowerDegree51Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x))))))=(boundaryFullPowerDegree51Block11Norm x).val+(boundaryFullPowerDegree51Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block11Norm x).property (boundaryFullPowerDegree51Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block11Norm,boundaryFullPowerDegree51Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x))=c} := by

  have he : ((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x))=(boundaryRePowerRow77_18Degree51Norm x).val+(boundaryRePowerRow77_19Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree51Norm x).property (boundaryRePowerRow77_19Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree51Norm,boundaryRePowerRow77_19Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x))))=(boundaryRePowerRow77_17Degree51Norm x).val+(boundaryFullPowerDegree51Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree51Norm x).property (boundaryFullPowerDegree51Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree51Norm,boundaryFullPowerDegree51Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))=c} := by

  have he : ((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))=(boundaryRePowerRow77_21Degree51Norm x).val+(boundaryRePowerRow77_22Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree51Norm x).property (boundaryRePowerRow77_22Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree51Norm,boundaryRePowerRow77_22Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))=(boundaryRePowerRow77_20Degree51Norm x).val+(boundaryFullPowerDegree51Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree51Norm x).property (boundaryFullPowerDegree51Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree51Norm,boundaryFullPowerDegree51Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))))=(boundaryFullPowerDegree51Block16Norm x).val+(boundaryFullPowerDegree51Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block16Norm x).property (boundaryFullPowerDegree51Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block16Norm,boundaryFullPowerDegree51Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))))))=(boundaryFullPowerDegree51Block14Norm x).val+(boundaryFullPowerDegree51Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block14Norm x).property (boundaryFullPowerDegree51Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block14Norm,boundaryFullPowerDegree51Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x)))))))))+(((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x)))))))))+(((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x))))))))))=(boundaryFullPowerDegree51Block9Norm x).val+(boundaryFullPowerDegree51Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block9Norm x).property (boundaryFullPowerDegree51Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block9Norm,boundaryFullPowerDegree51Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x))=c} := by

  have he : ((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x))=(boundaryImPowerRow77_0Degree51Norm x).val+(boundaryImPowerRow77_1Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree51Norm x).property (boundaryImPowerRow77_1Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree51Norm,boundaryImPowerRow77_1Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x))=c} := by

  have he : ((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x))=(boundaryImPowerRow77_3Degree51Norm x).val+(boundaryImPowerRow77_4Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree51Norm x).property (boundaryImPowerRow77_4Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree51Norm,boundaryImPowerRow77_4Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x))))=(boundaryImPowerRow77_2Degree51Norm x).val+(boundaryFullPowerDegree51Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree51Norm x).property (boundaryFullPowerDegree51Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree51Norm,boundaryFullPowerDegree51Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x))))))=(boundaryFullPowerDegree51Block22Norm x).val+(boundaryFullPowerDegree51Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block22Norm x).property (boundaryFullPowerDegree51Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block22Norm,boundaryFullPowerDegree51Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x))=c} := by

  have he : ((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x))=(boundaryImPowerRow77_6Degree51Norm x).val+(boundaryImPowerRow77_7Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree51Norm x).property (boundaryImPowerRow77_7Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree51Norm,boundaryImPowerRow77_7Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x))))=(boundaryImPowerRow77_5Degree51Norm x).val+(boundaryFullPowerDegree51Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree51Norm x).property (boundaryFullPowerDegree51Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree51Norm,boundaryFullPowerDegree51Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))=c} := by

  have he : ((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))=(boundaryImPowerRow77_9Degree51Norm x).val+(boundaryImPowerRow77_10Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree51Norm x).property (boundaryImPowerRow77_10Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree51Norm,boundaryImPowerRow77_10Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))))=(boundaryImPowerRow77_8Degree51Norm x).val+(boundaryFullPowerDegree51Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree51Norm x).property (boundaryFullPowerDegree51Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree51Norm,boundaryFullPowerDegree51Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))))))=(boundaryFullPowerDegree51Block27Norm x).val+(boundaryFullPowerDegree51Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block27Norm x).property (boundaryFullPowerDegree51Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block27Norm,boundaryFullPowerDegree51Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x))))))))=(boundaryFullPowerDegree51Block25Norm x).val+(boundaryFullPowerDegree51Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block25Norm x).property (boundaryFullPowerDegree51Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block25Norm,boundaryFullPowerDegree51Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x))=c} := by

  have he : ((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x))=(boundaryImPowerRow77_12Degree51Norm x).val+(boundaryImPowerRow77_13Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree51Norm x).property (boundaryImPowerRow77_13Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree51Norm,boundaryImPowerRow77_13Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x))))=(boundaryImPowerRow77_11Degree51Norm x).val+(boundaryFullPowerDegree51Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree51Norm x).property (boundaryFullPowerDegree51Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree51Norm,boundaryFullPowerDegree51Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x))=c} := by

  have he : ((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x))=(boundaryImPowerRow77_15Degree51Norm x).val+(boundaryImPowerRow77_16Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree51Norm x).property (boundaryImPowerRow77_16Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree51Norm,boundaryImPowerRow77_16Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x))))=(boundaryImPowerRow77_14Degree51Norm x).val+(boundaryFullPowerDegree51Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree51Norm x).property (boundaryFullPowerDegree51Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree51Norm,boundaryFullPowerDegree51Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x))))))=(boundaryFullPowerDegree51Block33Norm x).val+(boundaryFullPowerDegree51Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block33Norm x).property (boundaryFullPowerDegree51Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block33Norm,boundaryFullPowerDegree51Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x))=c} := by

  have he : ((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x))=(boundaryImPowerRow77_18Degree51Norm x).val+(boundaryImPowerRow77_19Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree51Norm x).property (boundaryImPowerRow77_19Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree51Norm,boundaryImPowerRow77_19Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x))))=(boundaryImPowerRow77_17Degree51Norm x).val+(boundaryFullPowerDegree51Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree51Norm x).property (boundaryFullPowerDegree51Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree51Norm,boundaryFullPowerDegree51Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))=c} := by

  have he : ((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))=(boundaryImPowerRow77_21Degree51Norm x).val+(boundaryLowPowerRow77Degree51Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree51Norm x).property (boundaryLowPowerRow77Degree51Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree51Norm,boundaryLowPowerRow77Degree51Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))=(boundaryImPowerRow77_20Degree51Norm x).val+(boundaryFullPowerDegree51Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree51Norm x).property (boundaryFullPowerDegree51Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree51Norm,boundaryFullPowerDegree51Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))=(boundaryFullPowerDegree51Block38Norm x).val+(boundaryFullPowerDegree51Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block38Norm x).property (boundaryFullPowerDegree51Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block38Norm,boundaryFullPowerDegree51Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))))=(boundaryFullPowerDegree51Block36Norm x).val+(boundaryFullPowerDegree51Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block36Norm x).property (boundaryFullPowerDegree51Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block36Norm,boundaryFullPowerDegree51Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x)))))))))+(((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x)))))))))+(((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))))))=(boundaryFullPowerDegree51Block31Norm x).val+(boundaryFullPowerDegree51Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block31Norm x).property (boundaryFullPowerDegree51Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block31Norm,boundaryFullPowerDegree51Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree51Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x)))))))))+(((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x)))))))))))+(((((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x)))))))))+(((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x)))))))))+(((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x)))))))))))+(((((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x)))))))))+(((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x))))))))))))=(boundaryFullPowerDegree51Block21Norm x).val+(boundaryFullPowerDegree51Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree51Block21Norm x).property (boundaryFullPowerDegree51Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block21Norm,boundaryFullPowerDegree51Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree51Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 51 x=c} := by

  have he0 : boundaryFullPowerRow77 51 x=((((((((((boundaryRePowerRow77_0 51 x)+(boundaryRePowerRow77_1 51 x)))+(((boundaryRePowerRow77_2 51 x)+(((boundaryRePowerRow77_3 51 x)+(boundaryRePowerRow77_4 51 x)))))))+(((((boundaryRePowerRow77_5 51 x)+(((boundaryRePowerRow77_6 51 x)+(boundaryRePowerRow77_7 51 x)))))+(((boundaryRePowerRow77_8 51 x)+(((boundaryRePowerRow77_9 51 x)+(boundaryRePowerRow77_10 51 x)))))))))+(((((((boundaryRePowerRow77_11 51 x)+(((boundaryRePowerRow77_12 51 x)+(boundaryRePowerRow77_13 51 x)))))+(((boundaryRePowerRow77_14 51 x)+(((boundaryRePowerRow77_15 51 x)+(boundaryRePowerRow77_16 51 x)))))))+(((((boundaryRePowerRow77_17 51 x)+(((boundaryRePowerRow77_18 51 x)+(boundaryRePowerRow77_19 51 x)))))+(((boundaryRePowerRow77_20 51 x)+(((boundaryRePowerRow77_21 51 x)+(boundaryRePowerRow77_22 51 x)))))))))))+(((((((((boundaryImPowerRow77_0 51 x)+(boundaryImPowerRow77_1 51 x)))+(((boundaryImPowerRow77_2 51 x)+(((boundaryImPowerRow77_3 51 x)+(boundaryImPowerRow77_4 51 x)))))))+(((((boundaryImPowerRow77_5 51 x)+(((boundaryImPowerRow77_6 51 x)+(boundaryImPowerRow77_7 51 x)))))+(((boundaryImPowerRow77_8 51 x)+(((boundaryImPowerRow77_9 51 x)+(boundaryImPowerRow77_10 51 x)))))))))+(((((((boundaryImPowerRow77_11 51 x)+(((boundaryImPowerRow77_12 51 x)+(boundaryImPowerRow77_13 51 x)))))+(((boundaryImPowerRow77_14 51 x)+(((boundaryImPowerRow77_15 51 x)+(boundaryImPowerRow77_16 51 x)))))))+(((((boundaryImPowerRow77_17 51 x)+(((boundaryImPowerRow77_18 51 x)+(boundaryImPowerRow77_19 51 x)))))+(((boundaryImPowerRow77_20 51 x)+(((boundaryImPowerRow77_21 51 x)+(boundaryLowPowerRow77 51 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree51Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree51Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
