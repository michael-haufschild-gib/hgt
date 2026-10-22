import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree71Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree71Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x))=c} := by

  have he : ((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x))=(boundaryRePowerRow77_0Degree71Norm x).val+(boundaryRePowerRow77_1Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree71Norm x).property (boundaryRePowerRow77_1Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree71Norm,boundaryRePowerRow77_1Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x))=c} := by

  have he : ((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x))=(boundaryRePowerRow77_3Degree71Norm x).val+(boundaryRePowerRow77_4Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree71Norm x).property (boundaryRePowerRow77_4Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree71Norm,boundaryRePowerRow77_4Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x))))=(boundaryRePowerRow77_2Degree71Norm x).val+(boundaryFullPowerDegree71Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree71Norm x).property (boundaryFullPowerDegree71Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree71Norm,boundaryFullPowerDegree71Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x))))))=(boundaryFullPowerDegree71Block0Norm x).val+(boundaryFullPowerDegree71Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block0Norm x).property (boundaryFullPowerDegree71Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block0Norm,boundaryFullPowerDegree71Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x))=c} := by

  have he : ((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x))=(boundaryRePowerRow77_6Degree71Norm x).val+(boundaryRePowerRow77_7Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree71Norm x).property (boundaryRePowerRow77_7Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree71Norm,boundaryRePowerRow77_7Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x))))=(boundaryRePowerRow77_5Degree71Norm x).val+(boundaryFullPowerDegree71Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree71Norm x).property (boundaryFullPowerDegree71Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree71Norm,boundaryFullPowerDegree71Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))=c} := by

  have he : ((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))=(boundaryRePowerRow77_9Degree71Norm x).val+(boundaryRePowerRow77_10Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree71Norm x).property (boundaryRePowerRow77_10Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree71Norm,boundaryRePowerRow77_10Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))))=(boundaryRePowerRow77_8Degree71Norm x).val+(boundaryFullPowerDegree71Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree71Norm x).property (boundaryFullPowerDegree71Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree71Norm,boundaryFullPowerDegree71Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))))))=(boundaryFullPowerDegree71Block5Norm x).val+(boundaryFullPowerDegree71Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block5Norm x).property (boundaryFullPowerDegree71Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block5Norm,boundaryFullPowerDegree71Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x))))))))=(boundaryFullPowerDegree71Block3Norm x).val+(boundaryFullPowerDegree71Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block3Norm x).property (boundaryFullPowerDegree71Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block3Norm,boundaryFullPowerDegree71Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x))=c} := by

  have he : ((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x))=(boundaryRePowerRow77_12Degree71Norm x).val+(boundaryRePowerRow77_13Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree71Norm x).property (boundaryRePowerRow77_13Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree71Norm,boundaryRePowerRow77_13Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x))))=(boundaryRePowerRow77_11Degree71Norm x).val+(boundaryFullPowerDegree71Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree71Norm x).property (boundaryFullPowerDegree71Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree71Norm,boundaryFullPowerDegree71Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x))=c} := by

  have he : ((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x))=(boundaryRePowerRow77_15Degree71Norm x).val+(boundaryRePowerRow77_16Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree71Norm x).property (boundaryRePowerRow77_16Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree71Norm,boundaryRePowerRow77_16Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x))))=(boundaryRePowerRow77_14Degree71Norm x).val+(boundaryFullPowerDegree71Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree71Norm x).property (boundaryFullPowerDegree71Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree71Norm,boundaryFullPowerDegree71Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x))))))=(boundaryFullPowerDegree71Block11Norm x).val+(boundaryFullPowerDegree71Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block11Norm x).property (boundaryFullPowerDegree71Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block11Norm,boundaryFullPowerDegree71Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x))=c} := by

  have he : ((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x))=(boundaryRePowerRow77_18Degree71Norm x).val+(boundaryRePowerRow77_19Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree71Norm x).property (boundaryRePowerRow77_19Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree71Norm,boundaryRePowerRow77_19Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x))))=(boundaryRePowerRow77_17Degree71Norm x).val+(boundaryFullPowerDegree71Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree71Norm x).property (boundaryFullPowerDegree71Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree71Norm,boundaryFullPowerDegree71Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))=c} := by

  have he : ((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))=(boundaryRePowerRow77_21Degree71Norm x).val+(boundaryRePowerRow77_22Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree71Norm x).property (boundaryRePowerRow77_22Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree71Norm,boundaryRePowerRow77_22Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))=(boundaryRePowerRow77_20Degree71Norm x).val+(boundaryFullPowerDegree71Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree71Norm x).property (boundaryFullPowerDegree71Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree71Norm,boundaryFullPowerDegree71Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))))=(boundaryFullPowerDegree71Block16Norm x).val+(boundaryFullPowerDegree71Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block16Norm x).property (boundaryFullPowerDegree71Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block16Norm,boundaryFullPowerDegree71Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))))))=(boundaryFullPowerDegree71Block14Norm x).val+(boundaryFullPowerDegree71Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block14Norm x).property (boundaryFullPowerDegree71Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block14Norm,boundaryFullPowerDegree71Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x)))))))))+(((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x)))))))))+(((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x))))))))))=(boundaryFullPowerDegree71Block9Norm x).val+(boundaryFullPowerDegree71Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block9Norm x).property (boundaryFullPowerDegree71Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block9Norm,boundaryFullPowerDegree71Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x))=c} := by

  have he : ((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x))=(boundaryImPowerRow77_0Degree71Norm x).val+(boundaryImPowerRow77_1Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree71Norm x).property (boundaryImPowerRow77_1Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree71Norm,boundaryImPowerRow77_1Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x))=c} := by

  have he : ((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x))=(boundaryImPowerRow77_3Degree71Norm x).val+(boundaryImPowerRow77_4Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree71Norm x).property (boundaryImPowerRow77_4Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree71Norm,boundaryImPowerRow77_4Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x))))=(boundaryImPowerRow77_2Degree71Norm x).val+(boundaryFullPowerDegree71Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree71Norm x).property (boundaryFullPowerDegree71Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree71Norm,boundaryFullPowerDegree71Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x))))))=(boundaryFullPowerDegree71Block22Norm x).val+(boundaryFullPowerDegree71Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block22Norm x).property (boundaryFullPowerDegree71Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block22Norm,boundaryFullPowerDegree71Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x))=c} := by

  have he : ((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x))=(boundaryImPowerRow77_6Degree71Norm x).val+(boundaryImPowerRow77_7Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree71Norm x).property (boundaryImPowerRow77_7Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree71Norm,boundaryImPowerRow77_7Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x))))=(boundaryImPowerRow77_5Degree71Norm x).val+(boundaryFullPowerDegree71Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree71Norm x).property (boundaryFullPowerDegree71Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree71Norm,boundaryFullPowerDegree71Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))=c} := by

  have he : ((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))=(boundaryImPowerRow77_9Degree71Norm x).val+(boundaryImPowerRow77_10Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree71Norm x).property (boundaryImPowerRow77_10Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree71Norm,boundaryImPowerRow77_10Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))))=(boundaryImPowerRow77_8Degree71Norm x).val+(boundaryFullPowerDegree71Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree71Norm x).property (boundaryFullPowerDegree71Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree71Norm,boundaryFullPowerDegree71Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))))))=(boundaryFullPowerDegree71Block27Norm x).val+(boundaryFullPowerDegree71Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block27Norm x).property (boundaryFullPowerDegree71Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block27Norm,boundaryFullPowerDegree71Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x))))))))=(boundaryFullPowerDegree71Block25Norm x).val+(boundaryFullPowerDegree71Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block25Norm x).property (boundaryFullPowerDegree71Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block25Norm,boundaryFullPowerDegree71Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x))=c} := by

  have he : ((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x))=(boundaryImPowerRow77_12Degree71Norm x).val+(boundaryImPowerRow77_13Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree71Norm x).property (boundaryImPowerRow77_13Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree71Norm,boundaryImPowerRow77_13Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x))))=(boundaryImPowerRow77_11Degree71Norm x).val+(boundaryFullPowerDegree71Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree71Norm x).property (boundaryFullPowerDegree71Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree71Norm,boundaryFullPowerDegree71Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x))=c} := by

  have he : ((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x))=(boundaryImPowerRow77_15Degree71Norm x).val+(boundaryImPowerRow77_16Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree71Norm x).property (boundaryImPowerRow77_16Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree71Norm,boundaryImPowerRow77_16Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x))))=(boundaryImPowerRow77_14Degree71Norm x).val+(boundaryFullPowerDegree71Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree71Norm x).property (boundaryFullPowerDegree71Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree71Norm,boundaryFullPowerDegree71Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x))))))=(boundaryFullPowerDegree71Block33Norm x).val+(boundaryFullPowerDegree71Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block33Norm x).property (boundaryFullPowerDegree71Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block33Norm,boundaryFullPowerDegree71Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x))=c} := by

  have he : ((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x))=(boundaryImPowerRow77_18Degree71Norm x).val+(boundaryImPowerRow77_19Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree71Norm x).property (boundaryImPowerRow77_19Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree71Norm,boundaryImPowerRow77_19Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x))))=(boundaryImPowerRow77_17Degree71Norm x).val+(boundaryFullPowerDegree71Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree71Norm x).property (boundaryFullPowerDegree71Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree71Norm,boundaryFullPowerDegree71Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))=c} := by

  have he : ((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))=(boundaryImPowerRow77_21Degree71Norm x).val+(boundaryLowPowerRow77Degree71Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree71Norm x).property (boundaryLowPowerRow77Degree71Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree71Norm,boundaryLowPowerRow77Degree71Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))=(boundaryImPowerRow77_20Degree71Norm x).val+(boundaryFullPowerDegree71Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree71Norm x).property (boundaryFullPowerDegree71Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree71Norm,boundaryFullPowerDegree71Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))=(boundaryFullPowerDegree71Block38Norm x).val+(boundaryFullPowerDegree71Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block38Norm x).property (boundaryFullPowerDegree71Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block38Norm,boundaryFullPowerDegree71Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))))=(boundaryFullPowerDegree71Block36Norm x).val+(boundaryFullPowerDegree71Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block36Norm x).property (boundaryFullPowerDegree71Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block36Norm,boundaryFullPowerDegree71Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x)))))))))+(((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x)))))))))+(((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))))))=(boundaryFullPowerDegree71Block31Norm x).val+(boundaryFullPowerDegree71Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block31Norm x).property (boundaryFullPowerDegree71Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block31Norm,boundaryFullPowerDegree71Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree71Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x)))))))))+(((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x)))))))))))+(((((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x)))))))))+(((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x)))))))))+(((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x)))))))))))+(((((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x)))))))))+(((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x))))))))))))=(boundaryFullPowerDegree71Block21Norm x).val+(boundaryFullPowerDegree71Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree71Block21Norm x).property (boundaryFullPowerDegree71Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block21Norm,boundaryFullPowerDegree71Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree71Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 71 x=c} := by

  have he0 : boundaryFullPowerRow77 71 x=((((((((((boundaryRePowerRow77_0 71 x)+(boundaryRePowerRow77_1 71 x)))+(((boundaryRePowerRow77_2 71 x)+(((boundaryRePowerRow77_3 71 x)+(boundaryRePowerRow77_4 71 x)))))))+(((((boundaryRePowerRow77_5 71 x)+(((boundaryRePowerRow77_6 71 x)+(boundaryRePowerRow77_7 71 x)))))+(((boundaryRePowerRow77_8 71 x)+(((boundaryRePowerRow77_9 71 x)+(boundaryRePowerRow77_10 71 x)))))))))+(((((((boundaryRePowerRow77_11 71 x)+(((boundaryRePowerRow77_12 71 x)+(boundaryRePowerRow77_13 71 x)))))+(((boundaryRePowerRow77_14 71 x)+(((boundaryRePowerRow77_15 71 x)+(boundaryRePowerRow77_16 71 x)))))))+(((((boundaryRePowerRow77_17 71 x)+(((boundaryRePowerRow77_18 71 x)+(boundaryRePowerRow77_19 71 x)))))+(((boundaryRePowerRow77_20 71 x)+(((boundaryRePowerRow77_21 71 x)+(boundaryRePowerRow77_22 71 x)))))))))))+(((((((((boundaryImPowerRow77_0 71 x)+(boundaryImPowerRow77_1 71 x)))+(((boundaryImPowerRow77_2 71 x)+(((boundaryImPowerRow77_3 71 x)+(boundaryImPowerRow77_4 71 x)))))))+(((((boundaryImPowerRow77_5 71 x)+(((boundaryImPowerRow77_6 71 x)+(boundaryImPowerRow77_7 71 x)))))+(((boundaryImPowerRow77_8 71 x)+(((boundaryImPowerRow77_9 71 x)+(boundaryImPowerRow77_10 71 x)))))))))+(((((((boundaryImPowerRow77_11 71 x)+(((boundaryImPowerRow77_12 71 x)+(boundaryImPowerRow77_13 71 x)))))+(((boundaryImPowerRow77_14 71 x)+(((boundaryImPowerRow77_15 71 x)+(boundaryImPowerRow77_16 71 x)))))))+(((((boundaryImPowerRow77_17 71 x)+(((boundaryImPowerRow77_18 71 x)+(boundaryImPowerRow77_19 71 x)))))+(((boundaryImPowerRow77_20 71 x)+(((boundaryImPowerRow77_21 71 x)+(boundaryLowPowerRow77 71 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree71Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree71Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
