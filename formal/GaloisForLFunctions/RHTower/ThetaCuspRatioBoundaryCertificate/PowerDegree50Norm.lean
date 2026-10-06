import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree50Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree50Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x))=c} := by

  have he : ((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x))=(boundaryRePowerRow77_0Degree50Norm x).val+(boundaryRePowerRow77_1Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree50Norm x).property (boundaryRePowerRow77_1Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree50Norm,boundaryRePowerRow77_1Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x))=c} := by

  have he : ((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x))=(boundaryRePowerRow77_3Degree50Norm x).val+(boundaryRePowerRow77_4Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree50Norm x).property (boundaryRePowerRow77_4Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree50Norm,boundaryRePowerRow77_4Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x))))=(boundaryRePowerRow77_2Degree50Norm x).val+(boundaryFullPowerDegree50Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree50Norm x).property (boundaryFullPowerDegree50Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree50Norm,boundaryFullPowerDegree50Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x))))))=(boundaryFullPowerDegree50Block0Norm x).val+(boundaryFullPowerDegree50Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block0Norm x).property (boundaryFullPowerDegree50Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block0Norm,boundaryFullPowerDegree50Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x))=c} := by

  have he : ((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x))=(boundaryRePowerRow77_6Degree50Norm x).val+(boundaryRePowerRow77_7Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree50Norm x).property (boundaryRePowerRow77_7Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree50Norm,boundaryRePowerRow77_7Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x))))=(boundaryRePowerRow77_5Degree50Norm x).val+(boundaryFullPowerDegree50Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree50Norm x).property (boundaryFullPowerDegree50Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree50Norm,boundaryFullPowerDegree50Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))=c} := by

  have he : ((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))=(boundaryRePowerRow77_9Degree50Norm x).val+(boundaryRePowerRow77_10Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree50Norm x).property (boundaryRePowerRow77_10Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree50Norm,boundaryRePowerRow77_10Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))))=(boundaryRePowerRow77_8Degree50Norm x).val+(boundaryFullPowerDegree50Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree50Norm x).property (boundaryFullPowerDegree50Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree50Norm,boundaryFullPowerDegree50Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))))))=(boundaryFullPowerDegree50Block5Norm x).val+(boundaryFullPowerDegree50Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block5Norm x).property (boundaryFullPowerDegree50Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block5Norm,boundaryFullPowerDegree50Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x))))))))=(boundaryFullPowerDegree50Block3Norm x).val+(boundaryFullPowerDegree50Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block3Norm x).property (boundaryFullPowerDegree50Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block3Norm,boundaryFullPowerDegree50Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x))=c} := by

  have he : ((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x))=(boundaryRePowerRow77_12Degree50Norm x).val+(boundaryRePowerRow77_13Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree50Norm x).property (boundaryRePowerRow77_13Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree50Norm,boundaryRePowerRow77_13Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x))))=(boundaryRePowerRow77_11Degree50Norm x).val+(boundaryFullPowerDegree50Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree50Norm x).property (boundaryFullPowerDegree50Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree50Norm,boundaryFullPowerDegree50Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x))=c} := by

  have he : ((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x))=(boundaryRePowerRow77_15Degree50Norm x).val+(boundaryRePowerRow77_16Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree50Norm x).property (boundaryRePowerRow77_16Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree50Norm,boundaryRePowerRow77_16Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x))))=(boundaryRePowerRow77_14Degree50Norm x).val+(boundaryFullPowerDegree50Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree50Norm x).property (boundaryFullPowerDegree50Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree50Norm,boundaryFullPowerDegree50Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x))))))=(boundaryFullPowerDegree50Block11Norm x).val+(boundaryFullPowerDegree50Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block11Norm x).property (boundaryFullPowerDegree50Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block11Norm,boundaryFullPowerDegree50Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x))=c} := by

  have he : ((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x))=(boundaryRePowerRow77_18Degree50Norm x).val+(boundaryRePowerRow77_19Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree50Norm x).property (boundaryRePowerRow77_19Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree50Norm,boundaryRePowerRow77_19Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x))))=(boundaryRePowerRow77_17Degree50Norm x).val+(boundaryFullPowerDegree50Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree50Norm x).property (boundaryFullPowerDegree50Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree50Norm,boundaryFullPowerDegree50Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))=c} := by

  have he : ((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))=(boundaryRePowerRow77_21Degree50Norm x).val+(boundaryRePowerRow77_22Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree50Norm x).property (boundaryRePowerRow77_22Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree50Norm,boundaryRePowerRow77_22Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))=(boundaryRePowerRow77_20Degree50Norm x).val+(boundaryFullPowerDegree50Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree50Norm x).property (boundaryFullPowerDegree50Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree50Norm,boundaryFullPowerDegree50Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))))=(boundaryFullPowerDegree50Block16Norm x).val+(boundaryFullPowerDegree50Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block16Norm x).property (boundaryFullPowerDegree50Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block16Norm,boundaryFullPowerDegree50Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))))))=(boundaryFullPowerDegree50Block14Norm x).val+(boundaryFullPowerDegree50Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block14Norm x).property (boundaryFullPowerDegree50Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block14Norm,boundaryFullPowerDegree50Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x)))))))))+(((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x)))))))))+(((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x))))))))))=(boundaryFullPowerDegree50Block9Norm x).val+(boundaryFullPowerDegree50Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block9Norm x).property (boundaryFullPowerDegree50Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block9Norm,boundaryFullPowerDegree50Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x))=c} := by

  have he : ((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x))=(boundaryImPowerRow77_0Degree50Norm x).val+(boundaryImPowerRow77_1Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree50Norm x).property (boundaryImPowerRow77_1Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree50Norm,boundaryImPowerRow77_1Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x))=c} := by

  have he : ((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x))=(boundaryImPowerRow77_3Degree50Norm x).val+(boundaryImPowerRow77_4Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree50Norm x).property (boundaryImPowerRow77_4Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree50Norm,boundaryImPowerRow77_4Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x))))=(boundaryImPowerRow77_2Degree50Norm x).val+(boundaryFullPowerDegree50Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree50Norm x).property (boundaryFullPowerDegree50Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree50Norm,boundaryFullPowerDegree50Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x))))))=(boundaryFullPowerDegree50Block22Norm x).val+(boundaryFullPowerDegree50Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block22Norm x).property (boundaryFullPowerDegree50Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block22Norm,boundaryFullPowerDegree50Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x))=c} := by

  have he : ((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x))=(boundaryImPowerRow77_6Degree50Norm x).val+(boundaryImPowerRow77_7Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree50Norm x).property (boundaryImPowerRow77_7Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree50Norm,boundaryImPowerRow77_7Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x))))=(boundaryImPowerRow77_5Degree50Norm x).val+(boundaryFullPowerDegree50Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree50Norm x).property (boundaryFullPowerDegree50Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree50Norm,boundaryFullPowerDegree50Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))=c} := by

  have he : ((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))=(boundaryImPowerRow77_9Degree50Norm x).val+(boundaryImPowerRow77_10Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree50Norm x).property (boundaryImPowerRow77_10Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree50Norm,boundaryImPowerRow77_10Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))))=(boundaryImPowerRow77_8Degree50Norm x).val+(boundaryFullPowerDegree50Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree50Norm x).property (boundaryFullPowerDegree50Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree50Norm,boundaryFullPowerDegree50Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))))))=(boundaryFullPowerDegree50Block27Norm x).val+(boundaryFullPowerDegree50Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block27Norm x).property (boundaryFullPowerDegree50Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block27Norm,boundaryFullPowerDegree50Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x))))))))=(boundaryFullPowerDegree50Block25Norm x).val+(boundaryFullPowerDegree50Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block25Norm x).property (boundaryFullPowerDegree50Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block25Norm,boundaryFullPowerDegree50Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x))=c} := by

  have he : ((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x))=(boundaryImPowerRow77_12Degree50Norm x).val+(boundaryImPowerRow77_13Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree50Norm x).property (boundaryImPowerRow77_13Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree50Norm,boundaryImPowerRow77_13Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x))))=(boundaryImPowerRow77_11Degree50Norm x).val+(boundaryFullPowerDegree50Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree50Norm x).property (boundaryFullPowerDegree50Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree50Norm,boundaryFullPowerDegree50Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x))=c} := by

  have he : ((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x))=(boundaryImPowerRow77_15Degree50Norm x).val+(boundaryImPowerRow77_16Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree50Norm x).property (boundaryImPowerRow77_16Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree50Norm,boundaryImPowerRow77_16Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x))))=(boundaryImPowerRow77_14Degree50Norm x).val+(boundaryFullPowerDegree50Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree50Norm x).property (boundaryFullPowerDegree50Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree50Norm,boundaryFullPowerDegree50Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x))))))=(boundaryFullPowerDegree50Block33Norm x).val+(boundaryFullPowerDegree50Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block33Norm x).property (boundaryFullPowerDegree50Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block33Norm,boundaryFullPowerDegree50Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x))=c} := by

  have he : ((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x))=(boundaryImPowerRow77_18Degree50Norm x).val+(boundaryImPowerRow77_19Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree50Norm x).property (boundaryImPowerRow77_19Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree50Norm,boundaryImPowerRow77_19Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x))))=(boundaryImPowerRow77_17Degree50Norm x).val+(boundaryFullPowerDegree50Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree50Norm x).property (boundaryFullPowerDegree50Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree50Norm,boundaryFullPowerDegree50Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))=c} := by

  have he : ((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))=(boundaryImPowerRow77_21Degree50Norm x).val+(boundaryLowPowerRow77Degree50Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree50Norm x).property (boundaryLowPowerRow77Degree50Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree50Norm,boundaryLowPowerRow77Degree50Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))=(boundaryImPowerRow77_20Degree50Norm x).val+(boundaryFullPowerDegree50Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree50Norm x).property (boundaryFullPowerDegree50Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree50Norm,boundaryFullPowerDegree50Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))=(boundaryFullPowerDegree50Block38Norm x).val+(boundaryFullPowerDegree50Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block38Norm x).property (boundaryFullPowerDegree50Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block38Norm,boundaryFullPowerDegree50Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))))=(boundaryFullPowerDegree50Block36Norm x).val+(boundaryFullPowerDegree50Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block36Norm x).property (boundaryFullPowerDegree50Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block36Norm,boundaryFullPowerDegree50Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x)))))))))+(((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x)))))))))+(((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))))))=(boundaryFullPowerDegree50Block31Norm x).val+(boundaryFullPowerDegree50Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block31Norm x).property (boundaryFullPowerDegree50Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block31Norm,boundaryFullPowerDegree50Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree50Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x)))))))))+(((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x)))))))))))+(((((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x)))))))))+(((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x)))))))))+(((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x)))))))))))+(((((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x)))))))))+(((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x))))))))))))=(boundaryFullPowerDegree50Block21Norm x).val+(boundaryFullPowerDegree50Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree50Block21Norm x).property (boundaryFullPowerDegree50Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block21Norm,boundaryFullPowerDegree50Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree50Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 50 x=c} := by

  have he0 : boundaryFullPowerRow77 50 x=((((((((((boundaryRePowerRow77_0 50 x)+(boundaryRePowerRow77_1 50 x)))+(((boundaryRePowerRow77_2 50 x)+(((boundaryRePowerRow77_3 50 x)+(boundaryRePowerRow77_4 50 x)))))))+(((((boundaryRePowerRow77_5 50 x)+(((boundaryRePowerRow77_6 50 x)+(boundaryRePowerRow77_7 50 x)))))+(((boundaryRePowerRow77_8 50 x)+(((boundaryRePowerRow77_9 50 x)+(boundaryRePowerRow77_10 50 x)))))))))+(((((((boundaryRePowerRow77_11 50 x)+(((boundaryRePowerRow77_12 50 x)+(boundaryRePowerRow77_13 50 x)))))+(((boundaryRePowerRow77_14 50 x)+(((boundaryRePowerRow77_15 50 x)+(boundaryRePowerRow77_16 50 x)))))))+(((((boundaryRePowerRow77_17 50 x)+(((boundaryRePowerRow77_18 50 x)+(boundaryRePowerRow77_19 50 x)))))+(((boundaryRePowerRow77_20 50 x)+(((boundaryRePowerRow77_21 50 x)+(boundaryRePowerRow77_22 50 x)))))))))))+(((((((((boundaryImPowerRow77_0 50 x)+(boundaryImPowerRow77_1 50 x)))+(((boundaryImPowerRow77_2 50 x)+(((boundaryImPowerRow77_3 50 x)+(boundaryImPowerRow77_4 50 x)))))))+(((((boundaryImPowerRow77_5 50 x)+(((boundaryImPowerRow77_6 50 x)+(boundaryImPowerRow77_7 50 x)))))+(((boundaryImPowerRow77_8 50 x)+(((boundaryImPowerRow77_9 50 x)+(boundaryImPowerRow77_10 50 x)))))))))+(((((((boundaryImPowerRow77_11 50 x)+(((boundaryImPowerRow77_12 50 x)+(boundaryImPowerRow77_13 50 x)))))+(((boundaryImPowerRow77_14 50 x)+(((boundaryImPowerRow77_15 50 x)+(boundaryImPowerRow77_16 50 x)))))))+(((((boundaryImPowerRow77_17 50 x)+(((boundaryImPowerRow77_18 50 x)+(boundaryImPowerRow77_19 50 x)))))+(((boundaryImPowerRow77_20 50 x)+(((boundaryImPowerRow77_21 50 x)+(boundaryLowPowerRow77 50 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree50Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree50Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
