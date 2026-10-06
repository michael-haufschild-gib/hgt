import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree78Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree78Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x))=c} := by

  have he : ((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x))=(boundaryRePowerRow77_0Degree78Norm x).val+(boundaryRePowerRow77_1Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree78Norm x).property (boundaryRePowerRow77_1Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree78Norm,boundaryRePowerRow77_1Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x))=c} := by

  have he : ((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x))=(boundaryRePowerRow77_3Degree78Norm x).val+(boundaryRePowerRow77_4Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree78Norm x).property (boundaryRePowerRow77_4Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree78Norm,boundaryRePowerRow77_4Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x))))=(boundaryRePowerRow77_2Degree78Norm x).val+(boundaryFullPowerDegree78Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree78Norm x).property (boundaryFullPowerDegree78Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree78Norm,boundaryFullPowerDegree78Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x))))))=(boundaryFullPowerDegree78Block0Norm x).val+(boundaryFullPowerDegree78Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block0Norm x).property (boundaryFullPowerDegree78Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block0Norm,boundaryFullPowerDegree78Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x))=c} := by

  have he : ((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x))=(boundaryRePowerRow77_6Degree78Norm x).val+(boundaryRePowerRow77_7Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree78Norm x).property (boundaryRePowerRow77_7Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree78Norm,boundaryRePowerRow77_7Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x))))=(boundaryRePowerRow77_5Degree78Norm x).val+(boundaryFullPowerDegree78Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree78Norm x).property (boundaryFullPowerDegree78Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree78Norm,boundaryFullPowerDegree78Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))=c} := by

  have he : ((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))=(boundaryRePowerRow77_9Degree78Norm x).val+(boundaryRePowerRow77_10Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree78Norm x).property (boundaryRePowerRow77_10Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree78Norm,boundaryRePowerRow77_10Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))))=(boundaryRePowerRow77_8Degree78Norm x).val+(boundaryFullPowerDegree78Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree78Norm x).property (boundaryFullPowerDegree78Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree78Norm,boundaryFullPowerDegree78Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))))))=(boundaryFullPowerDegree78Block5Norm x).val+(boundaryFullPowerDegree78Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block5Norm x).property (boundaryFullPowerDegree78Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block5Norm,boundaryFullPowerDegree78Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x))))))))=(boundaryFullPowerDegree78Block3Norm x).val+(boundaryFullPowerDegree78Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block3Norm x).property (boundaryFullPowerDegree78Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block3Norm,boundaryFullPowerDegree78Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x))=c} := by

  have he : ((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x))=(boundaryRePowerRow77_12Degree78Norm x).val+(boundaryRePowerRow77_13Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree78Norm x).property (boundaryRePowerRow77_13Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree78Norm,boundaryRePowerRow77_13Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x))))=(boundaryRePowerRow77_11Degree78Norm x).val+(boundaryFullPowerDegree78Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree78Norm x).property (boundaryFullPowerDegree78Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree78Norm,boundaryFullPowerDegree78Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x))=c} := by

  have he : ((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x))=(boundaryRePowerRow77_15Degree78Norm x).val+(boundaryRePowerRow77_16Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree78Norm x).property (boundaryRePowerRow77_16Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree78Norm,boundaryRePowerRow77_16Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x))))=(boundaryRePowerRow77_14Degree78Norm x).val+(boundaryFullPowerDegree78Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree78Norm x).property (boundaryFullPowerDegree78Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree78Norm,boundaryFullPowerDegree78Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x))))))=(boundaryFullPowerDegree78Block11Norm x).val+(boundaryFullPowerDegree78Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block11Norm x).property (boundaryFullPowerDegree78Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block11Norm,boundaryFullPowerDegree78Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x))=c} := by

  have he : ((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x))=(boundaryRePowerRow77_18Degree78Norm x).val+(boundaryRePowerRow77_19Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree78Norm x).property (boundaryRePowerRow77_19Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree78Norm,boundaryRePowerRow77_19Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x))))=(boundaryRePowerRow77_17Degree78Norm x).val+(boundaryFullPowerDegree78Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree78Norm x).property (boundaryFullPowerDegree78Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree78Norm,boundaryFullPowerDegree78Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))=c} := by

  have he : ((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))=(boundaryRePowerRow77_21Degree78Norm x).val+(boundaryRePowerRow77_22Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree78Norm x).property (boundaryRePowerRow77_22Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree78Norm,boundaryRePowerRow77_22Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))=(boundaryRePowerRow77_20Degree78Norm x).val+(boundaryFullPowerDegree78Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree78Norm x).property (boundaryFullPowerDegree78Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree78Norm,boundaryFullPowerDegree78Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))))=(boundaryFullPowerDegree78Block16Norm x).val+(boundaryFullPowerDegree78Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block16Norm x).property (boundaryFullPowerDegree78Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block16Norm,boundaryFullPowerDegree78Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))))))=(boundaryFullPowerDegree78Block14Norm x).val+(boundaryFullPowerDegree78Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block14Norm x).property (boundaryFullPowerDegree78Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block14Norm,boundaryFullPowerDegree78Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x)))))))))+(((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x)))))))))+(((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x))))))))))=(boundaryFullPowerDegree78Block9Norm x).val+(boundaryFullPowerDegree78Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block9Norm x).property (boundaryFullPowerDegree78Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block9Norm,boundaryFullPowerDegree78Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x))=c} := by

  have he : ((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x))=(boundaryImPowerRow77_0Degree78Norm x).val+(boundaryImPowerRow77_1Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree78Norm x).property (boundaryImPowerRow77_1Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree78Norm,boundaryImPowerRow77_1Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x))=c} := by

  have he : ((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x))=(boundaryImPowerRow77_3Degree78Norm x).val+(boundaryImPowerRow77_4Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree78Norm x).property (boundaryImPowerRow77_4Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree78Norm,boundaryImPowerRow77_4Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x))))=(boundaryImPowerRow77_2Degree78Norm x).val+(boundaryFullPowerDegree78Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree78Norm x).property (boundaryFullPowerDegree78Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree78Norm,boundaryFullPowerDegree78Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x))))))=(boundaryFullPowerDegree78Block22Norm x).val+(boundaryFullPowerDegree78Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block22Norm x).property (boundaryFullPowerDegree78Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block22Norm,boundaryFullPowerDegree78Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x))=c} := by

  have he : ((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x))=(boundaryImPowerRow77_6Degree78Norm x).val+(boundaryImPowerRow77_7Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree78Norm x).property (boundaryImPowerRow77_7Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree78Norm,boundaryImPowerRow77_7Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x))))=(boundaryImPowerRow77_5Degree78Norm x).val+(boundaryFullPowerDegree78Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree78Norm x).property (boundaryFullPowerDegree78Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree78Norm,boundaryFullPowerDegree78Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))=c} := by

  have he : ((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))=(boundaryImPowerRow77_9Degree78Norm x).val+(boundaryImPowerRow77_10Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree78Norm x).property (boundaryImPowerRow77_10Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree78Norm,boundaryImPowerRow77_10Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))))=(boundaryImPowerRow77_8Degree78Norm x).val+(boundaryFullPowerDegree78Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree78Norm x).property (boundaryFullPowerDegree78Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree78Norm,boundaryFullPowerDegree78Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))))))=(boundaryFullPowerDegree78Block27Norm x).val+(boundaryFullPowerDegree78Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block27Norm x).property (boundaryFullPowerDegree78Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block27Norm,boundaryFullPowerDegree78Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x))))))))=(boundaryFullPowerDegree78Block25Norm x).val+(boundaryFullPowerDegree78Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block25Norm x).property (boundaryFullPowerDegree78Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block25Norm,boundaryFullPowerDegree78Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x))=c} := by

  have he : ((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x))=(boundaryImPowerRow77_12Degree78Norm x).val+(boundaryImPowerRow77_13Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree78Norm x).property (boundaryImPowerRow77_13Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree78Norm,boundaryImPowerRow77_13Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x))))=(boundaryImPowerRow77_11Degree78Norm x).val+(boundaryFullPowerDegree78Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree78Norm x).property (boundaryFullPowerDegree78Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree78Norm,boundaryFullPowerDegree78Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x))=c} := by

  have he : ((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x))=(boundaryImPowerRow77_15Degree78Norm x).val+(boundaryImPowerRow77_16Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree78Norm x).property (boundaryImPowerRow77_16Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree78Norm,boundaryImPowerRow77_16Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x))))=(boundaryImPowerRow77_14Degree78Norm x).val+(boundaryFullPowerDegree78Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree78Norm x).property (boundaryFullPowerDegree78Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree78Norm,boundaryFullPowerDegree78Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x))))))=(boundaryFullPowerDegree78Block33Norm x).val+(boundaryFullPowerDegree78Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block33Norm x).property (boundaryFullPowerDegree78Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block33Norm,boundaryFullPowerDegree78Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x))=c} := by

  have he : ((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x))=(boundaryImPowerRow77_18Degree78Norm x).val+(boundaryImPowerRow77_19Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree78Norm x).property (boundaryImPowerRow77_19Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree78Norm,boundaryImPowerRow77_19Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x))))=(boundaryImPowerRow77_17Degree78Norm x).val+(boundaryFullPowerDegree78Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree78Norm x).property (boundaryFullPowerDegree78Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree78Norm,boundaryFullPowerDegree78Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))=c} := by

  have he : ((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))=(boundaryImPowerRow77_21Degree78Norm x).val+(boundaryLowPowerRow77Degree78Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree78Norm x).property (boundaryLowPowerRow77Degree78Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree78Norm,boundaryLowPowerRow77Degree78Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))=(boundaryImPowerRow77_20Degree78Norm x).val+(boundaryFullPowerDegree78Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree78Norm x).property (boundaryFullPowerDegree78Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree78Norm,boundaryFullPowerDegree78Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))=(boundaryFullPowerDegree78Block38Norm x).val+(boundaryFullPowerDegree78Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block38Norm x).property (boundaryFullPowerDegree78Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block38Norm,boundaryFullPowerDegree78Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))))=(boundaryFullPowerDegree78Block36Norm x).val+(boundaryFullPowerDegree78Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block36Norm x).property (boundaryFullPowerDegree78Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block36Norm,boundaryFullPowerDegree78Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x)))))))))+(((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x)))))))))+(((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))))))=(boundaryFullPowerDegree78Block31Norm x).val+(boundaryFullPowerDegree78Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block31Norm x).property (boundaryFullPowerDegree78Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block31Norm,boundaryFullPowerDegree78Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree78Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x)))))))))+(((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x)))))))))))+(((((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x)))))))))+(((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x)))))))))+(((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x)))))))))))+(((((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x)))))))))+(((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x))))))))))))=(boundaryFullPowerDegree78Block21Norm x).val+(boundaryFullPowerDegree78Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree78Block21Norm x).property (boundaryFullPowerDegree78Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block21Norm,boundaryFullPowerDegree78Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree78Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 78 x=c} := by

  have he0 : boundaryFullPowerRow77 78 x=((((((((((boundaryRePowerRow77_0 78 x)+(boundaryRePowerRow77_1 78 x)))+(((boundaryRePowerRow77_2 78 x)+(((boundaryRePowerRow77_3 78 x)+(boundaryRePowerRow77_4 78 x)))))))+(((((boundaryRePowerRow77_5 78 x)+(((boundaryRePowerRow77_6 78 x)+(boundaryRePowerRow77_7 78 x)))))+(((boundaryRePowerRow77_8 78 x)+(((boundaryRePowerRow77_9 78 x)+(boundaryRePowerRow77_10 78 x)))))))))+(((((((boundaryRePowerRow77_11 78 x)+(((boundaryRePowerRow77_12 78 x)+(boundaryRePowerRow77_13 78 x)))))+(((boundaryRePowerRow77_14 78 x)+(((boundaryRePowerRow77_15 78 x)+(boundaryRePowerRow77_16 78 x)))))))+(((((boundaryRePowerRow77_17 78 x)+(((boundaryRePowerRow77_18 78 x)+(boundaryRePowerRow77_19 78 x)))))+(((boundaryRePowerRow77_20 78 x)+(((boundaryRePowerRow77_21 78 x)+(boundaryRePowerRow77_22 78 x)))))))))))+(((((((((boundaryImPowerRow77_0 78 x)+(boundaryImPowerRow77_1 78 x)))+(((boundaryImPowerRow77_2 78 x)+(((boundaryImPowerRow77_3 78 x)+(boundaryImPowerRow77_4 78 x)))))))+(((((boundaryImPowerRow77_5 78 x)+(((boundaryImPowerRow77_6 78 x)+(boundaryImPowerRow77_7 78 x)))))+(((boundaryImPowerRow77_8 78 x)+(((boundaryImPowerRow77_9 78 x)+(boundaryImPowerRow77_10 78 x)))))))))+(((((((boundaryImPowerRow77_11 78 x)+(((boundaryImPowerRow77_12 78 x)+(boundaryImPowerRow77_13 78 x)))))+(((boundaryImPowerRow77_14 78 x)+(((boundaryImPowerRow77_15 78 x)+(boundaryImPowerRow77_16 78 x)))))))+(((((boundaryImPowerRow77_17 78 x)+(((boundaryImPowerRow77_18 78 x)+(boundaryImPowerRow77_19 78 x)))))+(((boundaryImPowerRow77_20 78 x)+(((boundaryImPowerRow77_21 78 x)+(boundaryLowPowerRow77 78 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree78Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree78Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
