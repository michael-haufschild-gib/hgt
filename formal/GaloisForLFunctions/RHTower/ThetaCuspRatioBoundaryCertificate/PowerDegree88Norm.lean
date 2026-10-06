import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree88Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree88Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x))=c} := by

  have he : ((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x))=(boundaryRePowerRow77_0Degree88Norm x).val+(boundaryRePowerRow77_1Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree88Norm x).property (boundaryRePowerRow77_1Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree88Norm,boundaryRePowerRow77_1Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x))=c} := by

  have he : ((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x))=(boundaryRePowerRow77_3Degree88Norm x).val+(boundaryRePowerRow77_4Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree88Norm x).property (boundaryRePowerRow77_4Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree88Norm,boundaryRePowerRow77_4Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x))))=(boundaryRePowerRow77_2Degree88Norm x).val+(boundaryFullPowerDegree88Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree88Norm x).property (boundaryFullPowerDegree88Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree88Norm,boundaryFullPowerDegree88Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x))))))=(boundaryFullPowerDegree88Block0Norm x).val+(boundaryFullPowerDegree88Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block0Norm x).property (boundaryFullPowerDegree88Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block0Norm,boundaryFullPowerDegree88Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x))=c} := by

  have he : ((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x))=(boundaryRePowerRow77_6Degree88Norm x).val+(boundaryRePowerRow77_7Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree88Norm x).property (boundaryRePowerRow77_7Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree88Norm,boundaryRePowerRow77_7Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x))))=(boundaryRePowerRow77_5Degree88Norm x).val+(boundaryFullPowerDegree88Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree88Norm x).property (boundaryFullPowerDegree88Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree88Norm,boundaryFullPowerDegree88Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))=c} := by

  have he : ((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))=(boundaryRePowerRow77_9Degree88Norm x).val+(boundaryRePowerRow77_10Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree88Norm x).property (boundaryRePowerRow77_10Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree88Norm,boundaryRePowerRow77_10Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))))=(boundaryRePowerRow77_8Degree88Norm x).val+(boundaryFullPowerDegree88Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree88Norm x).property (boundaryFullPowerDegree88Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree88Norm,boundaryFullPowerDegree88Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))))))=(boundaryFullPowerDegree88Block5Norm x).val+(boundaryFullPowerDegree88Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block5Norm x).property (boundaryFullPowerDegree88Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block5Norm,boundaryFullPowerDegree88Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x))))))))=(boundaryFullPowerDegree88Block3Norm x).val+(boundaryFullPowerDegree88Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block3Norm x).property (boundaryFullPowerDegree88Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block3Norm,boundaryFullPowerDegree88Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x))=c} := by

  have he : ((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x))=(boundaryRePowerRow77_12Degree88Norm x).val+(boundaryRePowerRow77_13Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree88Norm x).property (boundaryRePowerRow77_13Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree88Norm,boundaryRePowerRow77_13Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x))))=(boundaryRePowerRow77_11Degree88Norm x).val+(boundaryFullPowerDegree88Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree88Norm x).property (boundaryFullPowerDegree88Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree88Norm,boundaryFullPowerDegree88Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x))=c} := by

  have he : ((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x))=(boundaryRePowerRow77_15Degree88Norm x).val+(boundaryRePowerRow77_16Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree88Norm x).property (boundaryRePowerRow77_16Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree88Norm,boundaryRePowerRow77_16Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x))))=(boundaryRePowerRow77_14Degree88Norm x).val+(boundaryFullPowerDegree88Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree88Norm x).property (boundaryFullPowerDegree88Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree88Norm,boundaryFullPowerDegree88Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x))))))=(boundaryFullPowerDegree88Block11Norm x).val+(boundaryFullPowerDegree88Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block11Norm x).property (boundaryFullPowerDegree88Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block11Norm,boundaryFullPowerDegree88Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x))=c} := by

  have he : ((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x))=(boundaryRePowerRow77_18Degree88Norm x).val+(boundaryRePowerRow77_19Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree88Norm x).property (boundaryRePowerRow77_19Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree88Norm,boundaryRePowerRow77_19Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x))))=(boundaryRePowerRow77_17Degree88Norm x).val+(boundaryFullPowerDegree88Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree88Norm x).property (boundaryFullPowerDegree88Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree88Norm,boundaryFullPowerDegree88Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))=c} := by

  have he : ((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))=(boundaryRePowerRow77_21Degree88Norm x).val+(boundaryRePowerRow77_22Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree88Norm x).property (boundaryRePowerRow77_22Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree88Norm,boundaryRePowerRow77_22Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))=(boundaryRePowerRow77_20Degree88Norm x).val+(boundaryFullPowerDegree88Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree88Norm x).property (boundaryFullPowerDegree88Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree88Norm,boundaryFullPowerDegree88Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))))=(boundaryFullPowerDegree88Block16Norm x).val+(boundaryFullPowerDegree88Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block16Norm x).property (boundaryFullPowerDegree88Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block16Norm,boundaryFullPowerDegree88Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))))))=(boundaryFullPowerDegree88Block14Norm x).val+(boundaryFullPowerDegree88Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block14Norm x).property (boundaryFullPowerDegree88Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block14Norm,boundaryFullPowerDegree88Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x)))))))))+(((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x)))))))))+(((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x))))))))))=(boundaryFullPowerDegree88Block9Norm x).val+(boundaryFullPowerDegree88Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block9Norm x).property (boundaryFullPowerDegree88Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block9Norm,boundaryFullPowerDegree88Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x))=c} := by

  have he : ((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x))=(boundaryImPowerRow77_0Degree88Norm x).val+(boundaryImPowerRow77_1Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree88Norm x).property (boundaryImPowerRow77_1Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree88Norm,boundaryImPowerRow77_1Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x))=c} := by

  have he : ((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x))=(boundaryImPowerRow77_3Degree88Norm x).val+(boundaryImPowerRow77_4Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree88Norm x).property (boundaryImPowerRow77_4Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree88Norm,boundaryImPowerRow77_4Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x))))=(boundaryImPowerRow77_2Degree88Norm x).val+(boundaryFullPowerDegree88Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree88Norm x).property (boundaryFullPowerDegree88Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree88Norm,boundaryFullPowerDegree88Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x))))))=(boundaryFullPowerDegree88Block22Norm x).val+(boundaryFullPowerDegree88Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block22Norm x).property (boundaryFullPowerDegree88Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block22Norm,boundaryFullPowerDegree88Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x))=c} := by

  have he : ((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x))=(boundaryImPowerRow77_6Degree88Norm x).val+(boundaryImPowerRow77_7Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree88Norm x).property (boundaryImPowerRow77_7Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree88Norm,boundaryImPowerRow77_7Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x))))=(boundaryImPowerRow77_5Degree88Norm x).val+(boundaryFullPowerDegree88Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree88Norm x).property (boundaryFullPowerDegree88Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree88Norm,boundaryFullPowerDegree88Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))=c} := by

  have he : ((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))=(boundaryImPowerRow77_9Degree88Norm x).val+(boundaryImPowerRow77_10Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree88Norm x).property (boundaryImPowerRow77_10Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree88Norm,boundaryImPowerRow77_10Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))))=(boundaryImPowerRow77_8Degree88Norm x).val+(boundaryFullPowerDegree88Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree88Norm x).property (boundaryFullPowerDegree88Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree88Norm,boundaryFullPowerDegree88Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))))))=(boundaryFullPowerDegree88Block27Norm x).val+(boundaryFullPowerDegree88Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block27Norm x).property (boundaryFullPowerDegree88Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block27Norm,boundaryFullPowerDegree88Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x))))))))=(boundaryFullPowerDegree88Block25Norm x).val+(boundaryFullPowerDegree88Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block25Norm x).property (boundaryFullPowerDegree88Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block25Norm,boundaryFullPowerDegree88Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x))=c} := by

  have he : ((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x))=(boundaryImPowerRow77_12Degree88Norm x).val+(boundaryImPowerRow77_13Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree88Norm x).property (boundaryImPowerRow77_13Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree88Norm,boundaryImPowerRow77_13Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x))))=(boundaryImPowerRow77_11Degree88Norm x).val+(boundaryFullPowerDegree88Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree88Norm x).property (boundaryFullPowerDegree88Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree88Norm,boundaryFullPowerDegree88Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x))=c} := by

  have he : ((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x))=(boundaryImPowerRow77_15Degree88Norm x).val+(boundaryImPowerRow77_16Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree88Norm x).property (boundaryImPowerRow77_16Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree88Norm,boundaryImPowerRow77_16Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x))))=(boundaryImPowerRow77_14Degree88Norm x).val+(boundaryFullPowerDegree88Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree88Norm x).property (boundaryFullPowerDegree88Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree88Norm,boundaryFullPowerDegree88Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x))))))=(boundaryFullPowerDegree88Block33Norm x).val+(boundaryFullPowerDegree88Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block33Norm x).property (boundaryFullPowerDegree88Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block33Norm,boundaryFullPowerDegree88Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x))=c} := by

  have he : ((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x))=(boundaryImPowerRow77_18Degree88Norm x).val+(boundaryImPowerRow77_19Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree88Norm x).property (boundaryImPowerRow77_19Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree88Norm,boundaryImPowerRow77_19Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x))))=(boundaryImPowerRow77_17Degree88Norm x).val+(boundaryFullPowerDegree88Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree88Norm x).property (boundaryFullPowerDegree88Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree88Norm,boundaryFullPowerDegree88Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))=c} := by

  have he : ((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))=(boundaryImPowerRow77_21Degree88Norm x).val+(boundaryLowPowerRow77Degree88Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree88Norm x).property (boundaryLowPowerRow77Degree88Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree88Norm,boundaryLowPowerRow77Degree88Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))=(boundaryImPowerRow77_20Degree88Norm x).val+(boundaryFullPowerDegree88Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree88Norm x).property (boundaryFullPowerDegree88Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree88Norm,boundaryFullPowerDegree88Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))=(boundaryFullPowerDegree88Block38Norm x).val+(boundaryFullPowerDegree88Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block38Norm x).property (boundaryFullPowerDegree88Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block38Norm,boundaryFullPowerDegree88Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))))=(boundaryFullPowerDegree88Block36Norm x).val+(boundaryFullPowerDegree88Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block36Norm x).property (boundaryFullPowerDegree88Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block36Norm,boundaryFullPowerDegree88Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x)))))))))+(((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x)))))))))+(((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))))))=(boundaryFullPowerDegree88Block31Norm x).val+(boundaryFullPowerDegree88Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block31Norm x).property (boundaryFullPowerDegree88Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block31Norm,boundaryFullPowerDegree88Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree88Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x)))))))))+(((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x)))))))))))+(((((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x)))))))))+(((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x)))))))))+(((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x)))))))))))+(((((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x)))))))))+(((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x))))))))))))=(boundaryFullPowerDegree88Block21Norm x).val+(boundaryFullPowerDegree88Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree88Block21Norm x).property (boundaryFullPowerDegree88Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block21Norm,boundaryFullPowerDegree88Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree88Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 88 x=c} := by

  have he0 : boundaryFullPowerRow77 88 x=((((((((((boundaryRePowerRow77_0 88 x)+(boundaryRePowerRow77_1 88 x)))+(((boundaryRePowerRow77_2 88 x)+(((boundaryRePowerRow77_3 88 x)+(boundaryRePowerRow77_4 88 x)))))))+(((((boundaryRePowerRow77_5 88 x)+(((boundaryRePowerRow77_6 88 x)+(boundaryRePowerRow77_7 88 x)))))+(((boundaryRePowerRow77_8 88 x)+(((boundaryRePowerRow77_9 88 x)+(boundaryRePowerRow77_10 88 x)))))))))+(((((((boundaryRePowerRow77_11 88 x)+(((boundaryRePowerRow77_12 88 x)+(boundaryRePowerRow77_13 88 x)))))+(((boundaryRePowerRow77_14 88 x)+(((boundaryRePowerRow77_15 88 x)+(boundaryRePowerRow77_16 88 x)))))))+(((((boundaryRePowerRow77_17 88 x)+(((boundaryRePowerRow77_18 88 x)+(boundaryRePowerRow77_19 88 x)))))+(((boundaryRePowerRow77_20 88 x)+(((boundaryRePowerRow77_21 88 x)+(boundaryRePowerRow77_22 88 x)))))))))))+(((((((((boundaryImPowerRow77_0 88 x)+(boundaryImPowerRow77_1 88 x)))+(((boundaryImPowerRow77_2 88 x)+(((boundaryImPowerRow77_3 88 x)+(boundaryImPowerRow77_4 88 x)))))))+(((((boundaryImPowerRow77_5 88 x)+(((boundaryImPowerRow77_6 88 x)+(boundaryImPowerRow77_7 88 x)))))+(((boundaryImPowerRow77_8 88 x)+(((boundaryImPowerRow77_9 88 x)+(boundaryImPowerRow77_10 88 x)))))))))+(((((((boundaryImPowerRow77_11 88 x)+(((boundaryImPowerRow77_12 88 x)+(boundaryImPowerRow77_13 88 x)))))+(((boundaryImPowerRow77_14 88 x)+(((boundaryImPowerRow77_15 88 x)+(boundaryImPowerRow77_16 88 x)))))))+(((((boundaryImPowerRow77_17 88 x)+(((boundaryImPowerRow77_18 88 x)+(boundaryImPowerRow77_19 88 x)))))+(((boundaryImPowerRow77_20 88 x)+(((boundaryImPowerRow77_21 88 x)+(boundaryLowPowerRow77 88 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree88Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree88Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
