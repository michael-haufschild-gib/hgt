import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree5Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree5Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x))=c} := by

  have he : ((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x))=(boundaryRePowerRow77_0Degree5Norm x).val+(boundaryRePowerRow77_1Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree5Norm x).property (boundaryRePowerRow77_1Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree5Norm,boundaryRePowerRow77_1Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x))=c} := by

  have he : ((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x))=(boundaryRePowerRow77_3Degree5Norm x).val+(boundaryRePowerRow77_4Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree5Norm x).property (boundaryRePowerRow77_4Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree5Norm,boundaryRePowerRow77_4Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x))))=(boundaryRePowerRow77_2Degree5Norm x).val+(boundaryFullPowerDegree5Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree5Norm x).property (boundaryFullPowerDegree5Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree5Norm,boundaryFullPowerDegree5Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x))))))=(boundaryFullPowerDegree5Block0Norm x).val+(boundaryFullPowerDegree5Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block0Norm x).property (boundaryFullPowerDegree5Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block0Norm,boundaryFullPowerDegree5Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x))=c} := by

  have he : ((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x))=(boundaryRePowerRow77_6Degree5Norm x).val+(boundaryRePowerRow77_7Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree5Norm x).property (boundaryRePowerRow77_7Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree5Norm,boundaryRePowerRow77_7Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x))))=(boundaryRePowerRow77_5Degree5Norm x).val+(boundaryFullPowerDegree5Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree5Norm x).property (boundaryFullPowerDegree5Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree5Norm,boundaryFullPowerDegree5Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))=c} := by

  have he : ((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))=(boundaryRePowerRow77_9Degree5Norm x).val+(boundaryRePowerRow77_10Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree5Norm x).property (boundaryRePowerRow77_10Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree5Norm,boundaryRePowerRow77_10Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))))=(boundaryRePowerRow77_8Degree5Norm x).val+(boundaryFullPowerDegree5Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree5Norm x).property (boundaryFullPowerDegree5Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree5Norm,boundaryFullPowerDegree5Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))))))=(boundaryFullPowerDegree5Block5Norm x).val+(boundaryFullPowerDegree5Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block5Norm x).property (boundaryFullPowerDegree5Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block5Norm,boundaryFullPowerDegree5Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x))))))))=(boundaryFullPowerDegree5Block3Norm x).val+(boundaryFullPowerDegree5Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block3Norm x).property (boundaryFullPowerDegree5Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block3Norm,boundaryFullPowerDegree5Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x))=c} := by

  have he : ((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x))=(boundaryRePowerRow77_12Degree5Norm x).val+(boundaryRePowerRow77_13Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree5Norm x).property (boundaryRePowerRow77_13Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree5Norm,boundaryRePowerRow77_13Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x))))=(boundaryRePowerRow77_11Degree5Norm x).val+(boundaryFullPowerDegree5Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree5Norm x).property (boundaryFullPowerDegree5Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree5Norm,boundaryFullPowerDegree5Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x))=c} := by

  have he : ((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x))=(boundaryRePowerRow77_15Degree5Norm x).val+(boundaryRePowerRow77_16Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree5Norm x).property (boundaryRePowerRow77_16Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree5Norm,boundaryRePowerRow77_16Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x))))=(boundaryRePowerRow77_14Degree5Norm x).val+(boundaryFullPowerDegree5Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree5Norm x).property (boundaryFullPowerDegree5Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree5Norm,boundaryFullPowerDegree5Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x))))))=(boundaryFullPowerDegree5Block11Norm x).val+(boundaryFullPowerDegree5Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block11Norm x).property (boundaryFullPowerDegree5Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block11Norm,boundaryFullPowerDegree5Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x))=c} := by

  have he : ((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x))=(boundaryRePowerRow77_18Degree5Norm x).val+(boundaryRePowerRow77_19Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree5Norm x).property (boundaryRePowerRow77_19Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree5Norm,boundaryRePowerRow77_19Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x))))=(boundaryRePowerRow77_17Degree5Norm x).val+(boundaryFullPowerDegree5Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree5Norm x).property (boundaryFullPowerDegree5Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree5Norm,boundaryFullPowerDegree5Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))=c} := by

  have he : ((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))=(boundaryRePowerRow77_21Degree5Norm x).val+(boundaryRePowerRow77_22Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree5Norm x).property (boundaryRePowerRow77_22Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree5Norm,boundaryRePowerRow77_22Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))=(boundaryRePowerRow77_20Degree5Norm x).val+(boundaryFullPowerDegree5Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree5Norm x).property (boundaryFullPowerDegree5Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree5Norm,boundaryFullPowerDegree5Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))))=(boundaryFullPowerDegree5Block16Norm x).val+(boundaryFullPowerDegree5Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block16Norm x).property (boundaryFullPowerDegree5Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block16Norm,boundaryFullPowerDegree5Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))))))=(boundaryFullPowerDegree5Block14Norm x).val+(boundaryFullPowerDegree5Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block14Norm x).property (boundaryFullPowerDegree5Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block14Norm,boundaryFullPowerDegree5Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x)))))))))+(((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x)))))))))+(((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x))))))))))=(boundaryFullPowerDegree5Block9Norm x).val+(boundaryFullPowerDegree5Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block9Norm x).property (boundaryFullPowerDegree5Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block9Norm,boundaryFullPowerDegree5Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x))=c} := by

  have he : ((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x))=(boundaryImPowerRow77_0Degree5Norm x).val+(boundaryImPowerRow77_1Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree5Norm x).property (boundaryImPowerRow77_1Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree5Norm,boundaryImPowerRow77_1Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x))=c} := by

  have he : ((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x))=(boundaryImPowerRow77_3Degree5Norm x).val+(boundaryImPowerRow77_4Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree5Norm x).property (boundaryImPowerRow77_4Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree5Norm,boundaryImPowerRow77_4Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x))))=(boundaryImPowerRow77_2Degree5Norm x).val+(boundaryFullPowerDegree5Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree5Norm x).property (boundaryFullPowerDegree5Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree5Norm,boundaryFullPowerDegree5Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x))))))=(boundaryFullPowerDegree5Block22Norm x).val+(boundaryFullPowerDegree5Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block22Norm x).property (boundaryFullPowerDegree5Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block22Norm,boundaryFullPowerDegree5Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x))=c} := by

  have he : ((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x))=(boundaryImPowerRow77_6Degree5Norm x).val+(boundaryImPowerRow77_7Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree5Norm x).property (boundaryImPowerRow77_7Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree5Norm,boundaryImPowerRow77_7Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x))))=(boundaryImPowerRow77_5Degree5Norm x).val+(boundaryFullPowerDegree5Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree5Norm x).property (boundaryFullPowerDegree5Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree5Norm,boundaryFullPowerDegree5Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))=c} := by

  have he : ((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))=(boundaryImPowerRow77_9Degree5Norm x).val+(boundaryImPowerRow77_10Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree5Norm x).property (boundaryImPowerRow77_10Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree5Norm,boundaryImPowerRow77_10Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))))=(boundaryImPowerRow77_8Degree5Norm x).val+(boundaryFullPowerDegree5Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree5Norm x).property (boundaryFullPowerDegree5Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree5Norm,boundaryFullPowerDegree5Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))))))=(boundaryFullPowerDegree5Block27Norm x).val+(boundaryFullPowerDegree5Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block27Norm x).property (boundaryFullPowerDegree5Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block27Norm,boundaryFullPowerDegree5Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x))))))))=(boundaryFullPowerDegree5Block25Norm x).val+(boundaryFullPowerDegree5Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block25Norm x).property (boundaryFullPowerDegree5Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block25Norm,boundaryFullPowerDegree5Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x))=c} := by

  have he : ((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x))=(boundaryImPowerRow77_12Degree5Norm x).val+(boundaryImPowerRow77_13Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree5Norm x).property (boundaryImPowerRow77_13Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree5Norm,boundaryImPowerRow77_13Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x))))=(boundaryImPowerRow77_11Degree5Norm x).val+(boundaryFullPowerDegree5Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree5Norm x).property (boundaryFullPowerDegree5Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree5Norm,boundaryFullPowerDegree5Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x))=c} := by

  have he : ((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x))=(boundaryImPowerRow77_15Degree5Norm x).val+(boundaryImPowerRow77_16Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree5Norm x).property (boundaryImPowerRow77_16Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree5Norm,boundaryImPowerRow77_16Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x))))=(boundaryImPowerRow77_14Degree5Norm x).val+(boundaryFullPowerDegree5Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree5Norm x).property (boundaryFullPowerDegree5Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree5Norm,boundaryFullPowerDegree5Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x))))))=(boundaryFullPowerDegree5Block33Norm x).val+(boundaryFullPowerDegree5Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block33Norm x).property (boundaryFullPowerDegree5Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block33Norm,boundaryFullPowerDegree5Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x))=c} := by

  have he : ((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x))=(boundaryImPowerRow77_18Degree5Norm x).val+(boundaryImPowerRow77_19Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree5Norm x).property (boundaryImPowerRow77_19Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree5Norm,boundaryImPowerRow77_19Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x))))=(boundaryImPowerRow77_17Degree5Norm x).val+(boundaryFullPowerDegree5Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree5Norm x).property (boundaryFullPowerDegree5Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree5Norm,boundaryFullPowerDegree5Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))=c} := by

  have he : ((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))=(boundaryImPowerRow77_21Degree5Norm x).val+(boundaryLowPowerRow77Degree5Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree5Norm x).property (boundaryLowPowerRow77Degree5Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree5Norm,boundaryLowPowerRow77Degree5Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))=(boundaryImPowerRow77_20Degree5Norm x).val+(boundaryFullPowerDegree5Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree5Norm x).property (boundaryFullPowerDegree5Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree5Norm,boundaryFullPowerDegree5Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))=(boundaryFullPowerDegree5Block38Norm x).val+(boundaryFullPowerDegree5Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block38Norm x).property (boundaryFullPowerDegree5Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block38Norm,boundaryFullPowerDegree5Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))))=(boundaryFullPowerDegree5Block36Norm x).val+(boundaryFullPowerDegree5Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block36Norm x).property (boundaryFullPowerDegree5Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block36Norm,boundaryFullPowerDegree5Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x)))))))))+(((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x)))))))))+(((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))))))=(boundaryFullPowerDegree5Block31Norm x).val+(boundaryFullPowerDegree5Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block31Norm x).property (boundaryFullPowerDegree5Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block31Norm,boundaryFullPowerDegree5Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree5Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x)))))))))+(((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x)))))))))))+(((((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x)))))))))+(((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x)))))))))+(((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x)))))))))))+(((((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x)))))))))+(((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x))))))))))))=(boundaryFullPowerDegree5Block21Norm x).val+(boundaryFullPowerDegree5Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree5Block21Norm x).property (boundaryFullPowerDegree5Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block21Norm,boundaryFullPowerDegree5Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree5Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 5 x=c} := by

  have he0 : boundaryFullPowerRow77 5 x=((((((((((boundaryRePowerRow77_0 5 x)+(boundaryRePowerRow77_1 5 x)))+(((boundaryRePowerRow77_2 5 x)+(((boundaryRePowerRow77_3 5 x)+(boundaryRePowerRow77_4 5 x)))))))+(((((boundaryRePowerRow77_5 5 x)+(((boundaryRePowerRow77_6 5 x)+(boundaryRePowerRow77_7 5 x)))))+(((boundaryRePowerRow77_8 5 x)+(((boundaryRePowerRow77_9 5 x)+(boundaryRePowerRow77_10 5 x)))))))))+(((((((boundaryRePowerRow77_11 5 x)+(((boundaryRePowerRow77_12 5 x)+(boundaryRePowerRow77_13 5 x)))))+(((boundaryRePowerRow77_14 5 x)+(((boundaryRePowerRow77_15 5 x)+(boundaryRePowerRow77_16 5 x)))))))+(((((boundaryRePowerRow77_17 5 x)+(((boundaryRePowerRow77_18 5 x)+(boundaryRePowerRow77_19 5 x)))))+(((boundaryRePowerRow77_20 5 x)+(((boundaryRePowerRow77_21 5 x)+(boundaryRePowerRow77_22 5 x)))))))))))+(((((((((boundaryImPowerRow77_0 5 x)+(boundaryImPowerRow77_1 5 x)))+(((boundaryImPowerRow77_2 5 x)+(((boundaryImPowerRow77_3 5 x)+(boundaryImPowerRow77_4 5 x)))))))+(((((boundaryImPowerRow77_5 5 x)+(((boundaryImPowerRow77_6 5 x)+(boundaryImPowerRow77_7 5 x)))))+(((boundaryImPowerRow77_8 5 x)+(((boundaryImPowerRow77_9 5 x)+(boundaryImPowerRow77_10 5 x)))))))))+(((((((boundaryImPowerRow77_11 5 x)+(((boundaryImPowerRow77_12 5 x)+(boundaryImPowerRow77_13 5 x)))))+(((boundaryImPowerRow77_14 5 x)+(((boundaryImPowerRow77_15 5 x)+(boundaryImPowerRow77_16 5 x)))))))+(((((boundaryImPowerRow77_17 5 x)+(((boundaryImPowerRow77_18 5 x)+(boundaryImPowerRow77_19 5 x)))))+(((boundaryImPowerRow77_20 5 x)+(((boundaryImPowerRow77_21 5 x)+(boundaryLowPowerRow77 5 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree5Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree5Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
