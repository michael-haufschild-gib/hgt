import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree79Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree79Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x))=c} := by

  have he : ((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x))=(boundaryRePowerRow77_0Degree79Norm x).val+(boundaryRePowerRow77_1Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree79Norm x).property (boundaryRePowerRow77_1Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree79Norm,boundaryRePowerRow77_1Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x))=c} := by

  have he : ((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x))=(boundaryRePowerRow77_3Degree79Norm x).val+(boundaryRePowerRow77_4Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree79Norm x).property (boundaryRePowerRow77_4Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree79Norm,boundaryRePowerRow77_4Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x))))=(boundaryRePowerRow77_2Degree79Norm x).val+(boundaryFullPowerDegree79Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree79Norm x).property (boundaryFullPowerDegree79Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree79Norm,boundaryFullPowerDegree79Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x))))))=(boundaryFullPowerDegree79Block0Norm x).val+(boundaryFullPowerDegree79Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block0Norm x).property (boundaryFullPowerDegree79Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block0Norm,boundaryFullPowerDegree79Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x))=c} := by

  have he : ((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x))=(boundaryRePowerRow77_6Degree79Norm x).val+(boundaryRePowerRow77_7Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree79Norm x).property (boundaryRePowerRow77_7Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree79Norm,boundaryRePowerRow77_7Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x))))=(boundaryRePowerRow77_5Degree79Norm x).val+(boundaryFullPowerDegree79Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree79Norm x).property (boundaryFullPowerDegree79Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree79Norm,boundaryFullPowerDegree79Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))=c} := by

  have he : ((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))=(boundaryRePowerRow77_9Degree79Norm x).val+(boundaryRePowerRow77_10Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree79Norm x).property (boundaryRePowerRow77_10Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree79Norm,boundaryRePowerRow77_10Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))))=(boundaryRePowerRow77_8Degree79Norm x).val+(boundaryFullPowerDegree79Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree79Norm x).property (boundaryFullPowerDegree79Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree79Norm,boundaryFullPowerDegree79Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))))))=(boundaryFullPowerDegree79Block5Norm x).val+(boundaryFullPowerDegree79Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block5Norm x).property (boundaryFullPowerDegree79Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block5Norm,boundaryFullPowerDegree79Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x))))))))=(boundaryFullPowerDegree79Block3Norm x).val+(boundaryFullPowerDegree79Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block3Norm x).property (boundaryFullPowerDegree79Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block3Norm,boundaryFullPowerDegree79Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x))=c} := by

  have he : ((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x))=(boundaryRePowerRow77_12Degree79Norm x).val+(boundaryRePowerRow77_13Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree79Norm x).property (boundaryRePowerRow77_13Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree79Norm,boundaryRePowerRow77_13Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x))))=(boundaryRePowerRow77_11Degree79Norm x).val+(boundaryFullPowerDegree79Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree79Norm x).property (boundaryFullPowerDegree79Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree79Norm,boundaryFullPowerDegree79Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x))=c} := by

  have he : ((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x))=(boundaryRePowerRow77_15Degree79Norm x).val+(boundaryRePowerRow77_16Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree79Norm x).property (boundaryRePowerRow77_16Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree79Norm,boundaryRePowerRow77_16Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x))))=(boundaryRePowerRow77_14Degree79Norm x).val+(boundaryFullPowerDegree79Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree79Norm x).property (boundaryFullPowerDegree79Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree79Norm,boundaryFullPowerDegree79Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x))))))=(boundaryFullPowerDegree79Block11Norm x).val+(boundaryFullPowerDegree79Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block11Norm x).property (boundaryFullPowerDegree79Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block11Norm,boundaryFullPowerDegree79Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x))=c} := by

  have he : ((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x))=(boundaryRePowerRow77_18Degree79Norm x).val+(boundaryRePowerRow77_19Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree79Norm x).property (boundaryRePowerRow77_19Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree79Norm,boundaryRePowerRow77_19Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x))))=(boundaryRePowerRow77_17Degree79Norm x).val+(boundaryFullPowerDegree79Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree79Norm x).property (boundaryFullPowerDegree79Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree79Norm,boundaryFullPowerDegree79Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))=c} := by

  have he : ((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))=(boundaryRePowerRow77_21Degree79Norm x).val+(boundaryRePowerRow77_22Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree79Norm x).property (boundaryRePowerRow77_22Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree79Norm,boundaryRePowerRow77_22Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))=(boundaryRePowerRow77_20Degree79Norm x).val+(boundaryFullPowerDegree79Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree79Norm x).property (boundaryFullPowerDegree79Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree79Norm,boundaryFullPowerDegree79Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))))=(boundaryFullPowerDegree79Block16Norm x).val+(boundaryFullPowerDegree79Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block16Norm x).property (boundaryFullPowerDegree79Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block16Norm,boundaryFullPowerDegree79Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))))))=(boundaryFullPowerDegree79Block14Norm x).val+(boundaryFullPowerDegree79Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block14Norm x).property (boundaryFullPowerDegree79Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block14Norm,boundaryFullPowerDegree79Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x)))))))))+(((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x)))))))))+(((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x))))))))))=(boundaryFullPowerDegree79Block9Norm x).val+(boundaryFullPowerDegree79Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block9Norm x).property (boundaryFullPowerDegree79Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block9Norm,boundaryFullPowerDegree79Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x))=c} := by

  have he : ((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x))=(boundaryImPowerRow77_0Degree79Norm x).val+(boundaryImPowerRow77_1Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree79Norm x).property (boundaryImPowerRow77_1Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree79Norm,boundaryImPowerRow77_1Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x))=c} := by

  have he : ((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x))=(boundaryImPowerRow77_3Degree79Norm x).val+(boundaryImPowerRow77_4Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree79Norm x).property (boundaryImPowerRow77_4Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree79Norm,boundaryImPowerRow77_4Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x))))=(boundaryImPowerRow77_2Degree79Norm x).val+(boundaryFullPowerDegree79Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree79Norm x).property (boundaryFullPowerDegree79Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree79Norm,boundaryFullPowerDegree79Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x))))))=(boundaryFullPowerDegree79Block22Norm x).val+(boundaryFullPowerDegree79Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block22Norm x).property (boundaryFullPowerDegree79Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block22Norm,boundaryFullPowerDegree79Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x))=c} := by

  have he : ((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x))=(boundaryImPowerRow77_6Degree79Norm x).val+(boundaryImPowerRow77_7Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree79Norm x).property (boundaryImPowerRow77_7Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree79Norm,boundaryImPowerRow77_7Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x))))=(boundaryImPowerRow77_5Degree79Norm x).val+(boundaryFullPowerDegree79Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree79Norm x).property (boundaryFullPowerDegree79Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree79Norm,boundaryFullPowerDegree79Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))=c} := by

  have he : ((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))=(boundaryImPowerRow77_9Degree79Norm x).val+(boundaryImPowerRow77_10Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree79Norm x).property (boundaryImPowerRow77_10Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree79Norm,boundaryImPowerRow77_10Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))))=(boundaryImPowerRow77_8Degree79Norm x).val+(boundaryFullPowerDegree79Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree79Norm x).property (boundaryFullPowerDegree79Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree79Norm,boundaryFullPowerDegree79Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))))))=(boundaryFullPowerDegree79Block27Norm x).val+(boundaryFullPowerDegree79Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block27Norm x).property (boundaryFullPowerDegree79Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block27Norm,boundaryFullPowerDegree79Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x))))))))=(boundaryFullPowerDegree79Block25Norm x).val+(boundaryFullPowerDegree79Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block25Norm x).property (boundaryFullPowerDegree79Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block25Norm,boundaryFullPowerDegree79Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x))=c} := by

  have he : ((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x))=(boundaryImPowerRow77_12Degree79Norm x).val+(boundaryImPowerRow77_13Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree79Norm x).property (boundaryImPowerRow77_13Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree79Norm,boundaryImPowerRow77_13Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x))))=(boundaryImPowerRow77_11Degree79Norm x).val+(boundaryFullPowerDegree79Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree79Norm x).property (boundaryFullPowerDegree79Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree79Norm,boundaryFullPowerDegree79Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x))=c} := by

  have he : ((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x))=(boundaryImPowerRow77_15Degree79Norm x).val+(boundaryImPowerRow77_16Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree79Norm x).property (boundaryImPowerRow77_16Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree79Norm,boundaryImPowerRow77_16Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x))))=(boundaryImPowerRow77_14Degree79Norm x).val+(boundaryFullPowerDegree79Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree79Norm x).property (boundaryFullPowerDegree79Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree79Norm,boundaryFullPowerDegree79Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x))))))=(boundaryFullPowerDegree79Block33Norm x).val+(boundaryFullPowerDegree79Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block33Norm x).property (boundaryFullPowerDegree79Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block33Norm,boundaryFullPowerDegree79Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x))=c} := by

  have he : ((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x))=(boundaryImPowerRow77_18Degree79Norm x).val+(boundaryImPowerRow77_19Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree79Norm x).property (boundaryImPowerRow77_19Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree79Norm,boundaryImPowerRow77_19Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x))))=(boundaryImPowerRow77_17Degree79Norm x).val+(boundaryFullPowerDegree79Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree79Norm x).property (boundaryFullPowerDegree79Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree79Norm,boundaryFullPowerDegree79Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))=c} := by

  have he : ((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))=(boundaryImPowerRow77_21Degree79Norm x).val+(boundaryLowPowerRow77Degree79Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree79Norm x).property (boundaryLowPowerRow77Degree79Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree79Norm,boundaryLowPowerRow77Degree79Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))=(boundaryImPowerRow77_20Degree79Norm x).val+(boundaryFullPowerDegree79Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree79Norm x).property (boundaryFullPowerDegree79Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree79Norm,boundaryFullPowerDegree79Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))=(boundaryFullPowerDegree79Block38Norm x).val+(boundaryFullPowerDegree79Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block38Norm x).property (boundaryFullPowerDegree79Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block38Norm,boundaryFullPowerDegree79Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))))=(boundaryFullPowerDegree79Block36Norm x).val+(boundaryFullPowerDegree79Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block36Norm x).property (boundaryFullPowerDegree79Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block36Norm,boundaryFullPowerDegree79Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x)))))))))+(((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x)))))))))+(((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))))))=(boundaryFullPowerDegree79Block31Norm x).val+(boundaryFullPowerDegree79Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block31Norm x).property (boundaryFullPowerDegree79Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block31Norm,boundaryFullPowerDegree79Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree79Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x)))))))))+(((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x)))))))))))+(((((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x)))))))))+(((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x)))))))))+(((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x)))))))))))+(((((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x)))))))))+(((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x))))))))))))=(boundaryFullPowerDegree79Block21Norm x).val+(boundaryFullPowerDegree79Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree79Block21Norm x).property (boundaryFullPowerDegree79Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block21Norm,boundaryFullPowerDegree79Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree79Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 79 x=c} := by

  have he0 : boundaryFullPowerRow77 79 x=((((((((((boundaryRePowerRow77_0 79 x)+(boundaryRePowerRow77_1 79 x)))+(((boundaryRePowerRow77_2 79 x)+(((boundaryRePowerRow77_3 79 x)+(boundaryRePowerRow77_4 79 x)))))))+(((((boundaryRePowerRow77_5 79 x)+(((boundaryRePowerRow77_6 79 x)+(boundaryRePowerRow77_7 79 x)))))+(((boundaryRePowerRow77_8 79 x)+(((boundaryRePowerRow77_9 79 x)+(boundaryRePowerRow77_10 79 x)))))))))+(((((((boundaryRePowerRow77_11 79 x)+(((boundaryRePowerRow77_12 79 x)+(boundaryRePowerRow77_13 79 x)))))+(((boundaryRePowerRow77_14 79 x)+(((boundaryRePowerRow77_15 79 x)+(boundaryRePowerRow77_16 79 x)))))))+(((((boundaryRePowerRow77_17 79 x)+(((boundaryRePowerRow77_18 79 x)+(boundaryRePowerRow77_19 79 x)))))+(((boundaryRePowerRow77_20 79 x)+(((boundaryRePowerRow77_21 79 x)+(boundaryRePowerRow77_22 79 x)))))))))))+(((((((((boundaryImPowerRow77_0 79 x)+(boundaryImPowerRow77_1 79 x)))+(((boundaryImPowerRow77_2 79 x)+(((boundaryImPowerRow77_3 79 x)+(boundaryImPowerRow77_4 79 x)))))))+(((((boundaryImPowerRow77_5 79 x)+(((boundaryImPowerRow77_6 79 x)+(boundaryImPowerRow77_7 79 x)))))+(((boundaryImPowerRow77_8 79 x)+(((boundaryImPowerRow77_9 79 x)+(boundaryImPowerRow77_10 79 x)))))))))+(((((((boundaryImPowerRow77_11 79 x)+(((boundaryImPowerRow77_12 79 x)+(boundaryImPowerRow77_13 79 x)))))+(((boundaryImPowerRow77_14 79 x)+(((boundaryImPowerRow77_15 79 x)+(boundaryImPowerRow77_16 79 x)))))))+(((((boundaryImPowerRow77_17 79 x)+(((boundaryImPowerRow77_18 79 x)+(boundaryImPowerRow77_19 79 x)))))+(((boundaryImPowerRow77_20 79 x)+(((boundaryImPowerRow77_21 79 x)+(boundaryLowPowerRow77 79 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree79Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree79Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
