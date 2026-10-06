import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree83Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree83Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x))=c} := by

  have he : ((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x))=(boundaryRePowerRow77_0Degree83Norm x).val+(boundaryRePowerRow77_1Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree83Norm x).property (boundaryRePowerRow77_1Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree83Norm,boundaryRePowerRow77_1Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x))=c} := by

  have he : ((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x))=(boundaryRePowerRow77_3Degree83Norm x).val+(boundaryRePowerRow77_4Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree83Norm x).property (boundaryRePowerRow77_4Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree83Norm,boundaryRePowerRow77_4Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x))))=(boundaryRePowerRow77_2Degree83Norm x).val+(boundaryFullPowerDegree83Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree83Norm x).property (boundaryFullPowerDegree83Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree83Norm,boundaryFullPowerDegree83Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x))))))=(boundaryFullPowerDegree83Block0Norm x).val+(boundaryFullPowerDegree83Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block0Norm x).property (boundaryFullPowerDegree83Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block0Norm,boundaryFullPowerDegree83Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x))=c} := by

  have he : ((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x))=(boundaryRePowerRow77_6Degree83Norm x).val+(boundaryRePowerRow77_7Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree83Norm x).property (boundaryRePowerRow77_7Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree83Norm,boundaryRePowerRow77_7Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x))))=(boundaryRePowerRow77_5Degree83Norm x).val+(boundaryFullPowerDegree83Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree83Norm x).property (boundaryFullPowerDegree83Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree83Norm,boundaryFullPowerDegree83Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))=c} := by

  have he : ((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))=(boundaryRePowerRow77_9Degree83Norm x).val+(boundaryRePowerRow77_10Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree83Norm x).property (boundaryRePowerRow77_10Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree83Norm,boundaryRePowerRow77_10Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))))=(boundaryRePowerRow77_8Degree83Norm x).val+(boundaryFullPowerDegree83Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree83Norm x).property (boundaryFullPowerDegree83Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree83Norm,boundaryFullPowerDegree83Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))))))=(boundaryFullPowerDegree83Block5Norm x).val+(boundaryFullPowerDegree83Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block5Norm x).property (boundaryFullPowerDegree83Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block5Norm,boundaryFullPowerDegree83Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x))))))))=(boundaryFullPowerDegree83Block3Norm x).val+(boundaryFullPowerDegree83Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block3Norm x).property (boundaryFullPowerDegree83Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block3Norm,boundaryFullPowerDegree83Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x))=c} := by

  have he : ((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x))=(boundaryRePowerRow77_12Degree83Norm x).val+(boundaryRePowerRow77_13Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree83Norm x).property (boundaryRePowerRow77_13Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree83Norm,boundaryRePowerRow77_13Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x))))=(boundaryRePowerRow77_11Degree83Norm x).val+(boundaryFullPowerDegree83Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree83Norm x).property (boundaryFullPowerDegree83Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree83Norm,boundaryFullPowerDegree83Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x))=c} := by

  have he : ((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x))=(boundaryRePowerRow77_15Degree83Norm x).val+(boundaryRePowerRow77_16Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree83Norm x).property (boundaryRePowerRow77_16Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree83Norm,boundaryRePowerRow77_16Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x))))=(boundaryRePowerRow77_14Degree83Norm x).val+(boundaryFullPowerDegree83Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree83Norm x).property (boundaryFullPowerDegree83Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree83Norm,boundaryFullPowerDegree83Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x))))))=(boundaryFullPowerDegree83Block11Norm x).val+(boundaryFullPowerDegree83Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block11Norm x).property (boundaryFullPowerDegree83Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block11Norm,boundaryFullPowerDegree83Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x))=c} := by

  have he : ((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x))=(boundaryRePowerRow77_18Degree83Norm x).val+(boundaryRePowerRow77_19Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree83Norm x).property (boundaryRePowerRow77_19Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree83Norm,boundaryRePowerRow77_19Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x))))=(boundaryRePowerRow77_17Degree83Norm x).val+(boundaryFullPowerDegree83Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree83Norm x).property (boundaryFullPowerDegree83Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree83Norm,boundaryFullPowerDegree83Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))=c} := by

  have he : ((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))=(boundaryRePowerRow77_21Degree83Norm x).val+(boundaryRePowerRow77_22Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree83Norm x).property (boundaryRePowerRow77_22Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree83Norm,boundaryRePowerRow77_22Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))=(boundaryRePowerRow77_20Degree83Norm x).val+(boundaryFullPowerDegree83Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree83Norm x).property (boundaryFullPowerDegree83Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree83Norm,boundaryFullPowerDegree83Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))))=(boundaryFullPowerDegree83Block16Norm x).val+(boundaryFullPowerDegree83Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block16Norm x).property (boundaryFullPowerDegree83Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block16Norm,boundaryFullPowerDegree83Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))))))=(boundaryFullPowerDegree83Block14Norm x).val+(boundaryFullPowerDegree83Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block14Norm x).property (boundaryFullPowerDegree83Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block14Norm,boundaryFullPowerDegree83Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x)))))))))+(((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x)))))))))+(((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x))))))))))=(boundaryFullPowerDegree83Block9Norm x).val+(boundaryFullPowerDegree83Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block9Norm x).property (boundaryFullPowerDegree83Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block9Norm,boundaryFullPowerDegree83Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x))=c} := by

  have he : ((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x))=(boundaryImPowerRow77_0Degree83Norm x).val+(boundaryImPowerRow77_1Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree83Norm x).property (boundaryImPowerRow77_1Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree83Norm,boundaryImPowerRow77_1Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x))=c} := by

  have he : ((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x))=(boundaryImPowerRow77_3Degree83Norm x).val+(boundaryImPowerRow77_4Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree83Norm x).property (boundaryImPowerRow77_4Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree83Norm,boundaryImPowerRow77_4Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x))))=(boundaryImPowerRow77_2Degree83Norm x).val+(boundaryFullPowerDegree83Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree83Norm x).property (boundaryFullPowerDegree83Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree83Norm,boundaryFullPowerDegree83Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x))))))=(boundaryFullPowerDegree83Block22Norm x).val+(boundaryFullPowerDegree83Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block22Norm x).property (boundaryFullPowerDegree83Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block22Norm,boundaryFullPowerDegree83Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x))=c} := by

  have he : ((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x))=(boundaryImPowerRow77_6Degree83Norm x).val+(boundaryImPowerRow77_7Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree83Norm x).property (boundaryImPowerRow77_7Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree83Norm,boundaryImPowerRow77_7Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x))))=(boundaryImPowerRow77_5Degree83Norm x).val+(boundaryFullPowerDegree83Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree83Norm x).property (boundaryFullPowerDegree83Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree83Norm,boundaryFullPowerDegree83Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))=c} := by

  have he : ((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))=(boundaryImPowerRow77_9Degree83Norm x).val+(boundaryImPowerRow77_10Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree83Norm x).property (boundaryImPowerRow77_10Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree83Norm,boundaryImPowerRow77_10Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))))=(boundaryImPowerRow77_8Degree83Norm x).val+(boundaryFullPowerDegree83Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree83Norm x).property (boundaryFullPowerDegree83Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree83Norm,boundaryFullPowerDegree83Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))))))=(boundaryFullPowerDegree83Block27Norm x).val+(boundaryFullPowerDegree83Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block27Norm x).property (boundaryFullPowerDegree83Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block27Norm,boundaryFullPowerDegree83Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x))))))))=(boundaryFullPowerDegree83Block25Norm x).val+(boundaryFullPowerDegree83Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block25Norm x).property (boundaryFullPowerDegree83Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block25Norm,boundaryFullPowerDegree83Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x))=c} := by

  have he : ((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x))=(boundaryImPowerRow77_12Degree83Norm x).val+(boundaryImPowerRow77_13Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree83Norm x).property (boundaryImPowerRow77_13Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree83Norm,boundaryImPowerRow77_13Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x))))=(boundaryImPowerRow77_11Degree83Norm x).val+(boundaryFullPowerDegree83Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree83Norm x).property (boundaryFullPowerDegree83Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree83Norm,boundaryFullPowerDegree83Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x))=c} := by

  have he : ((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x))=(boundaryImPowerRow77_15Degree83Norm x).val+(boundaryImPowerRow77_16Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree83Norm x).property (boundaryImPowerRow77_16Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree83Norm,boundaryImPowerRow77_16Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x))))=(boundaryImPowerRow77_14Degree83Norm x).val+(boundaryFullPowerDegree83Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree83Norm x).property (boundaryFullPowerDegree83Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree83Norm,boundaryFullPowerDegree83Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x))))))=(boundaryFullPowerDegree83Block33Norm x).val+(boundaryFullPowerDegree83Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block33Norm x).property (boundaryFullPowerDegree83Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block33Norm,boundaryFullPowerDegree83Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x))=c} := by

  have he : ((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x))=(boundaryImPowerRow77_18Degree83Norm x).val+(boundaryImPowerRow77_19Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree83Norm x).property (boundaryImPowerRow77_19Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree83Norm,boundaryImPowerRow77_19Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x))))=(boundaryImPowerRow77_17Degree83Norm x).val+(boundaryFullPowerDegree83Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree83Norm x).property (boundaryFullPowerDegree83Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree83Norm,boundaryFullPowerDegree83Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))=c} := by

  have he : ((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))=(boundaryImPowerRow77_21Degree83Norm x).val+(boundaryLowPowerRow77Degree83Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree83Norm x).property (boundaryLowPowerRow77Degree83Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree83Norm,boundaryLowPowerRow77Degree83Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))=(boundaryImPowerRow77_20Degree83Norm x).val+(boundaryFullPowerDegree83Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree83Norm x).property (boundaryFullPowerDegree83Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree83Norm,boundaryFullPowerDegree83Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))=(boundaryFullPowerDegree83Block38Norm x).val+(boundaryFullPowerDegree83Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block38Norm x).property (boundaryFullPowerDegree83Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block38Norm,boundaryFullPowerDegree83Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))))=(boundaryFullPowerDegree83Block36Norm x).val+(boundaryFullPowerDegree83Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block36Norm x).property (boundaryFullPowerDegree83Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block36Norm,boundaryFullPowerDegree83Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x)))))))))+(((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x)))))))))+(((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))))))=(boundaryFullPowerDegree83Block31Norm x).val+(boundaryFullPowerDegree83Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block31Norm x).property (boundaryFullPowerDegree83Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block31Norm,boundaryFullPowerDegree83Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree83Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x)))))))))+(((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x)))))))))))+(((((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x)))))))))+(((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x)))))))))+(((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x)))))))))))+(((((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x)))))))))+(((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x))))))))))))=(boundaryFullPowerDegree83Block21Norm x).val+(boundaryFullPowerDegree83Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree83Block21Norm x).property (boundaryFullPowerDegree83Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block21Norm,boundaryFullPowerDegree83Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree83Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 83 x=c} := by

  have he0 : boundaryFullPowerRow77 83 x=((((((((((boundaryRePowerRow77_0 83 x)+(boundaryRePowerRow77_1 83 x)))+(((boundaryRePowerRow77_2 83 x)+(((boundaryRePowerRow77_3 83 x)+(boundaryRePowerRow77_4 83 x)))))))+(((((boundaryRePowerRow77_5 83 x)+(((boundaryRePowerRow77_6 83 x)+(boundaryRePowerRow77_7 83 x)))))+(((boundaryRePowerRow77_8 83 x)+(((boundaryRePowerRow77_9 83 x)+(boundaryRePowerRow77_10 83 x)))))))))+(((((((boundaryRePowerRow77_11 83 x)+(((boundaryRePowerRow77_12 83 x)+(boundaryRePowerRow77_13 83 x)))))+(((boundaryRePowerRow77_14 83 x)+(((boundaryRePowerRow77_15 83 x)+(boundaryRePowerRow77_16 83 x)))))))+(((((boundaryRePowerRow77_17 83 x)+(((boundaryRePowerRow77_18 83 x)+(boundaryRePowerRow77_19 83 x)))))+(((boundaryRePowerRow77_20 83 x)+(((boundaryRePowerRow77_21 83 x)+(boundaryRePowerRow77_22 83 x)))))))))))+(((((((((boundaryImPowerRow77_0 83 x)+(boundaryImPowerRow77_1 83 x)))+(((boundaryImPowerRow77_2 83 x)+(((boundaryImPowerRow77_3 83 x)+(boundaryImPowerRow77_4 83 x)))))))+(((((boundaryImPowerRow77_5 83 x)+(((boundaryImPowerRow77_6 83 x)+(boundaryImPowerRow77_7 83 x)))))+(((boundaryImPowerRow77_8 83 x)+(((boundaryImPowerRow77_9 83 x)+(boundaryImPowerRow77_10 83 x)))))))))+(((((((boundaryImPowerRow77_11 83 x)+(((boundaryImPowerRow77_12 83 x)+(boundaryImPowerRow77_13 83 x)))))+(((boundaryImPowerRow77_14 83 x)+(((boundaryImPowerRow77_15 83 x)+(boundaryImPowerRow77_16 83 x)))))))+(((((boundaryImPowerRow77_17 83 x)+(((boundaryImPowerRow77_18 83 x)+(boundaryImPowerRow77_19 83 x)))))+(((boundaryImPowerRow77_20 83 x)+(((boundaryImPowerRow77_21 83 x)+(boundaryLowPowerRow77 83 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree83Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree83Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
