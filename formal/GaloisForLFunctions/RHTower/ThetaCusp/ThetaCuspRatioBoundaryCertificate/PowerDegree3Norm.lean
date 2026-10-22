import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree3Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree3Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x))=c} := by

  have he : ((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x))=(boundaryRePowerRow77_0Degree3Norm x).val+(boundaryRePowerRow77_1Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree3Norm x).property (boundaryRePowerRow77_1Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree3Norm,boundaryRePowerRow77_1Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x))=c} := by

  have he : ((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x))=(boundaryRePowerRow77_3Degree3Norm x).val+(boundaryRePowerRow77_4Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree3Norm x).property (boundaryRePowerRow77_4Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree3Norm,boundaryRePowerRow77_4Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x))))=(boundaryRePowerRow77_2Degree3Norm x).val+(boundaryFullPowerDegree3Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree3Norm x).property (boundaryFullPowerDegree3Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree3Norm,boundaryFullPowerDegree3Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x))))))=(boundaryFullPowerDegree3Block0Norm x).val+(boundaryFullPowerDegree3Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block0Norm x).property (boundaryFullPowerDegree3Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block0Norm,boundaryFullPowerDegree3Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x))=c} := by

  have he : ((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x))=(boundaryRePowerRow77_6Degree3Norm x).val+(boundaryRePowerRow77_7Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree3Norm x).property (boundaryRePowerRow77_7Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree3Norm,boundaryRePowerRow77_7Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x))))=(boundaryRePowerRow77_5Degree3Norm x).val+(boundaryFullPowerDegree3Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree3Norm x).property (boundaryFullPowerDegree3Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree3Norm,boundaryFullPowerDegree3Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))=c} := by

  have he : ((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))=(boundaryRePowerRow77_9Degree3Norm x).val+(boundaryRePowerRow77_10Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree3Norm x).property (boundaryRePowerRow77_10Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree3Norm,boundaryRePowerRow77_10Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))))=(boundaryRePowerRow77_8Degree3Norm x).val+(boundaryFullPowerDegree3Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree3Norm x).property (boundaryFullPowerDegree3Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree3Norm,boundaryFullPowerDegree3Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))))))=(boundaryFullPowerDegree3Block5Norm x).val+(boundaryFullPowerDegree3Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block5Norm x).property (boundaryFullPowerDegree3Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block5Norm,boundaryFullPowerDegree3Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x))))))))=(boundaryFullPowerDegree3Block3Norm x).val+(boundaryFullPowerDegree3Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block3Norm x).property (boundaryFullPowerDegree3Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block3Norm,boundaryFullPowerDegree3Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x))=c} := by

  have he : ((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x))=(boundaryRePowerRow77_12Degree3Norm x).val+(boundaryRePowerRow77_13Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree3Norm x).property (boundaryRePowerRow77_13Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree3Norm,boundaryRePowerRow77_13Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x))))=(boundaryRePowerRow77_11Degree3Norm x).val+(boundaryFullPowerDegree3Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree3Norm x).property (boundaryFullPowerDegree3Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree3Norm,boundaryFullPowerDegree3Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x))=c} := by

  have he : ((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x))=(boundaryRePowerRow77_15Degree3Norm x).val+(boundaryRePowerRow77_16Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree3Norm x).property (boundaryRePowerRow77_16Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree3Norm,boundaryRePowerRow77_16Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x))))=(boundaryRePowerRow77_14Degree3Norm x).val+(boundaryFullPowerDegree3Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree3Norm x).property (boundaryFullPowerDegree3Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree3Norm,boundaryFullPowerDegree3Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x))))))=(boundaryFullPowerDegree3Block11Norm x).val+(boundaryFullPowerDegree3Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block11Norm x).property (boundaryFullPowerDegree3Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block11Norm,boundaryFullPowerDegree3Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x))=c} := by

  have he : ((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x))=(boundaryRePowerRow77_18Degree3Norm x).val+(boundaryRePowerRow77_19Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree3Norm x).property (boundaryRePowerRow77_19Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree3Norm,boundaryRePowerRow77_19Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x))))=(boundaryRePowerRow77_17Degree3Norm x).val+(boundaryFullPowerDegree3Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree3Norm x).property (boundaryFullPowerDegree3Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree3Norm,boundaryFullPowerDegree3Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))=c} := by

  have he : ((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))=(boundaryRePowerRow77_21Degree3Norm x).val+(boundaryRePowerRow77_22Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree3Norm x).property (boundaryRePowerRow77_22Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree3Norm,boundaryRePowerRow77_22Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))=(boundaryRePowerRow77_20Degree3Norm x).val+(boundaryFullPowerDegree3Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree3Norm x).property (boundaryFullPowerDegree3Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree3Norm,boundaryFullPowerDegree3Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))))=(boundaryFullPowerDegree3Block16Norm x).val+(boundaryFullPowerDegree3Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block16Norm x).property (boundaryFullPowerDegree3Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block16Norm,boundaryFullPowerDegree3Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))))))=(boundaryFullPowerDegree3Block14Norm x).val+(boundaryFullPowerDegree3Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block14Norm x).property (boundaryFullPowerDegree3Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block14Norm,boundaryFullPowerDegree3Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x)))))))))+(((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x)))))))))+(((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x))))))))))=(boundaryFullPowerDegree3Block9Norm x).val+(boundaryFullPowerDegree3Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block9Norm x).property (boundaryFullPowerDegree3Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block9Norm,boundaryFullPowerDegree3Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x))=c} := by

  have he : ((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x))=(boundaryImPowerRow77_0Degree3Norm x).val+(boundaryImPowerRow77_1Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree3Norm x).property (boundaryImPowerRow77_1Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree3Norm,boundaryImPowerRow77_1Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x))=c} := by

  have he : ((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x))=(boundaryImPowerRow77_3Degree3Norm x).val+(boundaryImPowerRow77_4Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree3Norm x).property (boundaryImPowerRow77_4Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree3Norm,boundaryImPowerRow77_4Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x))))=(boundaryImPowerRow77_2Degree3Norm x).val+(boundaryFullPowerDegree3Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree3Norm x).property (boundaryFullPowerDegree3Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree3Norm,boundaryFullPowerDegree3Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x))))))=(boundaryFullPowerDegree3Block22Norm x).val+(boundaryFullPowerDegree3Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block22Norm x).property (boundaryFullPowerDegree3Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block22Norm,boundaryFullPowerDegree3Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x))=c} := by

  have he : ((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x))=(boundaryImPowerRow77_6Degree3Norm x).val+(boundaryImPowerRow77_7Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree3Norm x).property (boundaryImPowerRow77_7Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree3Norm,boundaryImPowerRow77_7Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x))))=(boundaryImPowerRow77_5Degree3Norm x).val+(boundaryFullPowerDegree3Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree3Norm x).property (boundaryFullPowerDegree3Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree3Norm,boundaryFullPowerDegree3Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))=c} := by

  have he : ((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))=(boundaryImPowerRow77_9Degree3Norm x).val+(boundaryImPowerRow77_10Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree3Norm x).property (boundaryImPowerRow77_10Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree3Norm,boundaryImPowerRow77_10Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))))=(boundaryImPowerRow77_8Degree3Norm x).val+(boundaryFullPowerDegree3Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree3Norm x).property (boundaryFullPowerDegree3Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree3Norm,boundaryFullPowerDegree3Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))))))=(boundaryFullPowerDegree3Block27Norm x).val+(boundaryFullPowerDegree3Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block27Norm x).property (boundaryFullPowerDegree3Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block27Norm,boundaryFullPowerDegree3Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x))))))))=(boundaryFullPowerDegree3Block25Norm x).val+(boundaryFullPowerDegree3Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block25Norm x).property (boundaryFullPowerDegree3Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block25Norm,boundaryFullPowerDegree3Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x))=c} := by

  have he : ((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x))=(boundaryImPowerRow77_12Degree3Norm x).val+(boundaryImPowerRow77_13Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree3Norm x).property (boundaryImPowerRow77_13Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree3Norm,boundaryImPowerRow77_13Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x))))=(boundaryImPowerRow77_11Degree3Norm x).val+(boundaryFullPowerDegree3Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree3Norm x).property (boundaryFullPowerDegree3Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree3Norm,boundaryFullPowerDegree3Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x))=c} := by

  have he : ((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x))=(boundaryImPowerRow77_15Degree3Norm x).val+(boundaryImPowerRow77_16Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree3Norm x).property (boundaryImPowerRow77_16Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree3Norm,boundaryImPowerRow77_16Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x))))=(boundaryImPowerRow77_14Degree3Norm x).val+(boundaryFullPowerDegree3Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree3Norm x).property (boundaryFullPowerDegree3Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree3Norm,boundaryFullPowerDegree3Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x))))))=(boundaryFullPowerDegree3Block33Norm x).val+(boundaryFullPowerDegree3Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block33Norm x).property (boundaryFullPowerDegree3Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block33Norm,boundaryFullPowerDegree3Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x))=c} := by

  have he : ((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x))=(boundaryImPowerRow77_18Degree3Norm x).val+(boundaryImPowerRow77_19Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree3Norm x).property (boundaryImPowerRow77_19Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree3Norm,boundaryImPowerRow77_19Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x))))=(boundaryImPowerRow77_17Degree3Norm x).val+(boundaryFullPowerDegree3Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree3Norm x).property (boundaryFullPowerDegree3Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree3Norm,boundaryFullPowerDegree3Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))=c} := by

  have he : ((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))=(boundaryImPowerRow77_21Degree3Norm x).val+(boundaryLowPowerRow77Degree3Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree3Norm x).property (boundaryLowPowerRow77Degree3Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree3Norm,boundaryLowPowerRow77Degree3Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))=(boundaryImPowerRow77_20Degree3Norm x).val+(boundaryFullPowerDegree3Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree3Norm x).property (boundaryFullPowerDegree3Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree3Norm,boundaryFullPowerDegree3Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))=(boundaryFullPowerDegree3Block38Norm x).val+(boundaryFullPowerDegree3Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block38Norm x).property (boundaryFullPowerDegree3Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block38Norm,boundaryFullPowerDegree3Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))))=(boundaryFullPowerDegree3Block36Norm x).val+(boundaryFullPowerDegree3Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block36Norm x).property (boundaryFullPowerDegree3Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block36Norm,boundaryFullPowerDegree3Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x)))))))))+(((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x)))))))))+(((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))))))=(boundaryFullPowerDegree3Block31Norm x).val+(boundaryFullPowerDegree3Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block31Norm x).property (boundaryFullPowerDegree3Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block31Norm,boundaryFullPowerDegree3Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree3Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x)))))))))+(((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x)))))))))))+(((((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x)))))))))+(((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x)))))))))+(((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x)))))))))))+(((((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x)))))))))+(((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x))))))))))))=(boundaryFullPowerDegree3Block21Norm x).val+(boundaryFullPowerDegree3Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree3Block21Norm x).property (boundaryFullPowerDegree3Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block21Norm,boundaryFullPowerDegree3Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree3Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 3 x=c} := by

  have he0 : boundaryFullPowerRow77 3 x=((((((((((boundaryRePowerRow77_0 3 x)+(boundaryRePowerRow77_1 3 x)))+(((boundaryRePowerRow77_2 3 x)+(((boundaryRePowerRow77_3 3 x)+(boundaryRePowerRow77_4 3 x)))))))+(((((boundaryRePowerRow77_5 3 x)+(((boundaryRePowerRow77_6 3 x)+(boundaryRePowerRow77_7 3 x)))))+(((boundaryRePowerRow77_8 3 x)+(((boundaryRePowerRow77_9 3 x)+(boundaryRePowerRow77_10 3 x)))))))))+(((((((boundaryRePowerRow77_11 3 x)+(((boundaryRePowerRow77_12 3 x)+(boundaryRePowerRow77_13 3 x)))))+(((boundaryRePowerRow77_14 3 x)+(((boundaryRePowerRow77_15 3 x)+(boundaryRePowerRow77_16 3 x)))))))+(((((boundaryRePowerRow77_17 3 x)+(((boundaryRePowerRow77_18 3 x)+(boundaryRePowerRow77_19 3 x)))))+(((boundaryRePowerRow77_20 3 x)+(((boundaryRePowerRow77_21 3 x)+(boundaryRePowerRow77_22 3 x)))))))))))+(((((((((boundaryImPowerRow77_0 3 x)+(boundaryImPowerRow77_1 3 x)))+(((boundaryImPowerRow77_2 3 x)+(((boundaryImPowerRow77_3 3 x)+(boundaryImPowerRow77_4 3 x)))))))+(((((boundaryImPowerRow77_5 3 x)+(((boundaryImPowerRow77_6 3 x)+(boundaryImPowerRow77_7 3 x)))))+(((boundaryImPowerRow77_8 3 x)+(((boundaryImPowerRow77_9 3 x)+(boundaryImPowerRow77_10 3 x)))))))))+(((((((boundaryImPowerRow77_11 3 x)+(((boundaryImPowerRow77_12 3 x)+(boundaryImPowerRow77_13 3 x)))))+(((boundaryImPowerRow77_14 3 x)+(((boundaryImPowerRow77_15 3 x)+(boundaryImPowerRow77_16 3 x)))))))+(((((boundaryImPowerRow77_17 3 x)+(((boundaryImPowerRow77_18 3 x)+(boundaryImPowerRow77_19 3 x)))))+(((boundaryImPowerRow77_20 3 x)+(((boundaryImPowerRow77_21 3 x)+(boundaryLowPowerRow77 3 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree3Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree3Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
