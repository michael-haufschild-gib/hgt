import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree1Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree1Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x))=c} := by

  have he : ((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x))=(boundaryRePowerRow77_0Degree1Norm x).val+(boundaryRePowerRow77_1Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree1Norm x).property (boundaryRePowerRow77_1Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree1Norm,boundaryRePowerRow77_1Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x))=c} := by

  have he : ((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x))=(boundaryRePowerRow77_3Degree1Norm x).val+(boundaryRePowerRow77_4Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree1Norm x).property (boundaryRePowerRow77_4Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree1Norm,boundaryRePowerRow77_4Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x))))=(boundaryRePowerRow77_2Degree1Norm x).val+(boundaryFullPowerDegree1Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree1Norm x).property (boundaryFullPowerDegree1Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree1Norm,boundaryFullPowerDegree1Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x))))))=(boundaryFullPowerDegree1Block0Norm x).val+(boundaryFullPowerDegree1Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block0Norm x).property (boundaryFullPowerDegree1Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block0Norm,boundaryFullPowerDegree1Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x))=c} := by

  have he : ((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x))=(boundaryRePowerRow77_6Degree1Norm x).val+(boundaryRePowerRow77_7Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree1Norm x).property (boundaryRePowerRow77_7Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree1Norm,boundaryRePowerRow77_7Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x))))=(boundaryRePowerRow77_5Degree1Norm x).val+(boundaryFullPowerDegree1Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree1Norm x).property (boundaryFullPowerDegree1Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree1Norm,boundaryFullPowerDegree1Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))=c} := by

  have he : ((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))=(boundaryRePowerRow77_9Degree1Norm x).val+(boundaryRePowerRow77_10Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree1Norm x).property (boundaryRePowerRow77_10Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree1Norm,boundaryRePowerRow77_10Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))))=(boundaryRePowerRow77_8Degree1Norm x).val+(boundaryFullPowerDegree1Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree1Norm x).property (boundaryFullPowerDegree1Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree1Norm,boundaryFullPowerDegree1Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))))))=(boundaryFullPowerDegree1Block5Norm x).val+(boundaryFullPowerDegree1Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block5Norm x).property (boundaryFullPowerDegree1Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block5Norm,boundaryFullPowerDegree1Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x))))))))=(boundaryFullPowerDegree1Block3Norm x).val+(boundaryFullPowerDegree1Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block3Norm x).property (boundaryFullPowerDegree1Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block3Norm,boundaryFullPowerDegree1Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x))=c} := by

  have he : ((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x))=(boundaryRePowerRow77_12Degree1Norm x).val+(boundaryRePowerRow77_13Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree1Norm x).property (boundaryRePowerRow77_13Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree1Norm,boundaryRePowerRow77_13Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x))))=(boundaryRePowerRow77_11Degree1Norm x).val+(boundaryFullPowerDegree1Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree1Norm x).property (boundaryFullPowerDegree1Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree1Norm,boundaryFullPowerDegree1Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x))=c} := by

  have he : ((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x))=(boundaryRePowerRow77_15Degree1Norm x).val+(boundaryRePowerRow77_16Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree1Norm x).property (boundaryRePowerRow77_16Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree1Norm,boundaryRePowerRow77_16Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x))))=(boundaryRePowerRow77_14Degree1Norm x).val+(boundaryFullPowerDegree1Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree1Norm x).property (boundaryFullPowerDegree1Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree1Norm,boundaryFullPowerDegree1Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x))))))=(boundaryFullPowerDegree1Block11Norm x).val+(boundaryFullPowerDegree1Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block11Norm x).property (boundaryFullPowerDegree1Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block11Norm,boundaryFullPowerDegree1Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x))=c} := by

  have he : ((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x))=(boundaryRePowerRow77_18Degree1Norm x).val+(boundaryRePowerRow77_19Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree1Norm x).property (boundaryRePowerRow77_19Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree1Norm,boundaryRePowerRow77_19Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x))))=(boundaryRePowerRow77_17Degree1Norm x).val+(boundaryFullPowerDegree1Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree1Norm x).property (boundaryFullPowerDegree1Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree1Norm,boundaryFullPowerDegree1Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))=c} := by

  have he : ((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))=(boundaryRePowerRow77_21Degree1Norm x).val+(boundaryRePowerRow77_22Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree1Norm x).property (boundaryRePowerRow77_22Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree1Norm,boundaryRePowerRow77_22Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))=(boundaryRePowerRow77_20Degree1Norm x).val+(boundaryFullPowerDegree1Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree1Norm x).property (boundaryFullPowerDegree1Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree1Norm,boundaryFullPowerDegree1Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))))=(boundaryFullPowerDegree1Block16Norm x).val+(boundaryFullPowerDegree1Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block16Norm x).property (boundaryFullPowerDegree1Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block16Norm,boundaryFullPowerDegree1Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))))))=(boundaryFullPowerDegree1Block14Norm x).val+(boundaryFullPowerDegree1Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block14Norm x).property (boundaryFullPowerDegree1Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block14Norm,boundaryFullPowerDegree1Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x)))))))))+(((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x)))))))))+(((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x))))))))))=(boundaryFullPowerDegree1Block9Norm x).val+(boundaryFullPowerDegree1Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block9Norm x).property (boundaryFullPowerDegree1Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block9Norm,boundaryFullPowerDegree1Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x))=c} := by

  have he : ((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x))=(boundaryImPowerRow77_0Degree1Norm x).val+(boundaryImPowerRow77_1Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree1Norm x).property (boundaryImPowerRow77_1Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree1Norm,boundaryImPowerRow77_1Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x))=c} := by

  have he : ((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x))=(boundaryImPowerRow77_3Degree1Norm x).val+(boundaryImPowerRow77_4Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree1Norm x).property (boundaryImPowerRow77_4Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree1Norm,boundaryImPowerRow77_4Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x))))=(boundaryImPowerRow77_2Degree1Norm x).val+(boundaryFullPowerDegree1Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree1Norm x).property (boundaryFullPowerDegree1Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree1Norm,boundaryFullPowerDegree1Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x))))))=(boundaryFullPowerDegree1Block22Norm x).val+(boundaryFullPowerDegree1Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block22Norm x).property (boundaryFullPowerDegree1Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block22Norm,boundaryFullPowerDegree1Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x))=c} := by

  have he : ((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x))=(boundaryImPowerRow77_6Degree1Norm x).val+(boundaryImPowerRow77_7Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree1Norm x).property (boundaryImPowerRow77_7Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree1Norm,boundaryImPowerRow77_7Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x))))=(boundaryImPowerRow77_5Degree1Norm x).val+(boundaryFullPowerDegree1Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree1Norm x).property (boundaryFullPowerDegree1Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree1Norm,boundaryFullPowerDegree1Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))=c} := by

  have he : ((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))=(boundaryImPowerRow77_9Degree1Norm x).val+(boundaryImPowerRow77_10Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree1Norm x).property (boundaryImPowerRow77_10Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree1Norm,boundaryImPowerRow77_10Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))))=(boundaryImPowerRow77_8Degree1Norm x).val+(boundaryFullPowerDegree1Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree1Norm x).property (boundaryFullPowerDegree1Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree1Norm,boundaryFullPowerDegree1Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))))))=(boundaryFullPowerDegree1Block27Norm x).val+(boundaryFullPowerDegree1Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block27Norm x).property (boundaryFullPowerDegree1Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block27Norm,boundaryFullPowerDegree1Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x))))))))=(boundaryFullPowerDegree1Block25Norm x).val+(boundaryFullPowerDegree1Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block25Norm x).property (boundaryFullPowerDegree1Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block25Norm,boundaryFullPowerDegree1Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x))=c} := by

  have he : ((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x))=(boundaryImPowerRow77_12Degree1Norm x).val+(boundaryImPowerRow77_13Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree1Norm x).property (boundaryImPowerRow77_13Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree1Norm,boundaryImPowerRow77_13Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x))))=(boundaryImPowerRow77_11Degree1Norm x).val+(boundaryFullPowerDegree1Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree1Norm x).property (boundaryFullPowerDegree1Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree1Norm,boundaryFullPowerDegree1Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x))=c} := by

  have he : ((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x))=(boundaryImPowerRow77_15Degree1Norm x).val+(boundaryImPowerRow77_16Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree1Norm x).property (boundaryImPowerRow77_16Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree1Norm,boundaryImPowerRow77_16Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x))))=(boundaryImPowerRow77_14Degree1Norm x).val+(boundaryFullPowerDegree1Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree1Norm x).property (boundaryFullPowerDegree1Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree1Norm,boundaryFullPowerDegree1Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x))))))=(boundaryFullPowerDegree1Block33Norm x).val+(boundaryFullPowerDegree1Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block33Norm x).property (boundaryFullPowerDegree1Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block33Norm,boundaryFullPowerDegree1Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x))=c} := by

  have he : ((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x))=(boundaryImPowerRow77_18Degree1Norm x).val+(boundaryImPowerRow77_19Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree1Norm x).property (boundaryImPowerRow77_19Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree1Norm,boundaryImPowerRow77_19Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x))))=(boundaryImPowerRow77_17Degree1Norm x).val+(boundaryFullPowerDegree1Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree1Norm x).property (boundaryFullPowerDegree1Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree1Norm,boundaryFullPowerDegree1Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))=c} := by

  have he : ((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))=(boundaryImPowerRow77_21Degree1Norm x).val+(boundaryLowPowerRow77Degree1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree1Norm x).property (boundaryLowPowerRow77Degree1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree1Norm,boundaryLowPowerRow77Degree1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))=(boundaryImPowerRow77_20Degree1Norm x).val+(boundaryFullPowerDegree1Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree1Norm x).property (boundaryFullPowerDegree1Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree1Norm,boundaryFullPowerDegree1Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))=(boundaryFullPowerDegree1Block38Norm x).val+(boundaryFullPowerDegree1Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block38Norm x).property (boundaryFullPowerDegree1Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block38Norm,boundaryFullPowerDegree1Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))))=(boundaryFullPowerDegree1Block36Norm x).val+(boundaryFullPowerDegree1Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block36Norm x).property (boundaryFullPowerDegree1Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block36Norm,boundaryFullPowerDegree1Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x)))))))))+(((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x)))))))))+(((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))))))=(boundaryFullPowerDegree1Block31Norm x).val+(boundaryFullPowerDegree1Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block31Norm x).property (boundaryFullPowerDegree1Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block31Norm,boundaryFullPowerDegree1Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree1Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x)))))))))+(((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x)))))))))))+(((((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x)))))))))+(((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x)))))))))+(((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x)))))))))))+(((((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x)))))))))+(((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x))))))))))))=(boundaryFullPowerDegree1Block21Norm x).val+(boundaryFullPowerDegree1Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree1Block21Norm x).property (boundaryFullPowerDegree1Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block21Norm,boundaryFullPowerDegree1Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree1Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 1 x=c} := by

  have he0 : boundaryFullPowerRow77 1 x=((((((((((boundaryRePowerRow77_0 1 x)+(boundaryRePowerRow77_1 1 x)))+(((boundaryRePowerRow77_2 1 x)+(((boundaryRePowerRow77_3 1 x)+(boundaryRePowerRow77_4 1 x)))))))+(((((boundaryRePowerRow77_5 1 x)+(((boundaryRePowerRow77_6 1 x)+(boundaryRePowerRow77_7 1 x)))))+(((boundaryRePowerRow77_8 1 x)+(((boundaryRePowerRow77_9 1 x)+(boundaryRePowerRow77_10 1 x)))))))))+(((((((boundaryRePowerRow77_11 1 x)+(((boundaryRePowerRow77_12 1 x)+(boundaryRePowerRow77_13 1 x)))))+(((boundaryRePowerRow77_14 1 x)+(((boundaryRePowerRow77_15 1 x)+(boundaryRePowerRow77_16 1 x)))))))+(((((boundaryRePowerRow77_17 1 x)+(((boundaryRePowerRow77_18 1 x)+(boundaryRePowerRow77_19 1 x)))))+(((boundaryRePowerRow77_20 1 x)+(((boundaryRePowerRow77_21 1 x)+(boundaryRePowerRow77_22 1 x)))))))))))+(((((((((boundaryImPowerRow77_0 1 x)+(boundaryImPowerRow77_1 1 x)))+(((boundaryImPowerRow77_2 1 x)+(((boundaryImPowerRow77_3 1 x)+(boundaryImPowerRow77_4 1 x)))))))+(((((boundaryImPowerRow77_5 1 x)+(((boundaryImPowerRow77_6 1 x)+(boundaryImPowerRow77_7 1 x)))))+(((boundaryImPowerRow77_8 1 x)+(((boundaryImPowerRow77_9 1 x)+(boundaryImPowerRow77_10 1 x)))))))))+(((((((boundaryImPowerRow77_11 1 x)+(((boundaryImPowerRow77_12 1 x)+(boundaryImPowerRow77_13 1 x)))))+(((boundaryImPowerRow77_14 1 x)+(((boundaryImPowerRow77_15 1 x)+(boundaryImPowerRow77_16 1 x)))))))+(((((boundaryImPowerRow77_17 1 x)+(((boundaryImPowerRow77_18 1 x)+(boundaryImPowerRow77_19 1 x)))))+(((boundaryImPowerRow77_20 1 x)+(((boundaryImPowerRow77_21 1 x)+(boundaryLowPowerRow77 1 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree1Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree1Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
