import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree35Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree35Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x))=c} := by

  have he : ((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x))=(boundaryRePowerRow77_0Degree35Norm x).val+(boundaryRePowerRow77_1Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree35Norm x).property (boundaryRePowerRow77_1Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree35Norm,boundaryRePowerRow77_1Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x))=c} := by

  have he : ((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x))=(boundaryRePowerRow77_3Degree35Norm x).val+(boundaryRePowerRow77_4Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree35Norm x).property (boundaryRePowerRow77_4Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree35Norm,boundaryRePowerRow77_4Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x))))=(boundaryRePowerRow77_2Degree35Norm x).val+(boundaryFullPowerDegree35Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree35Norm x).property (boundaryFullPowerDegree35Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree35Norm,boundaryFullPowerDegree35Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x))))))=(boundaryFullPowerDegree35Block0Norm x).val+(boundaryFullPowerDegree35Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block0Norm x).property (boundaryFullPowerDegree35Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block0Norm,boundaryFullPowerDegree35Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x))=c} := by

  have he : ((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x))=(boundaryRePowerRow77_6Degree35Norm x).val+(boundaryRePowerRow77_7Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree35Norm x).property (boundaryRePowerRow77_7Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree35Norm,boundaryRePowerRow77_7Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x))))=(boundaryRePowerRow77_5Degree35Norm x).val+(boundaryFullPowerDegree35Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree35Norm x).property (boundaryFullPowerDegree35Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree35Norm,boundaryFullPowerDegree35Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))=c} := by

  have he : ((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))=(boundaryRePowerRow77_9Degree35Norm x).val+(boundaryRePowerRow77_10Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree35Norm x).property (boundaryRePowerRow77_10Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree35Norm,boundaryRePowerRow77_10Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))))=(boundaryRePowerRow77_8Degree35Norm x).val+(boundaryFullPowerDegree35Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree35Norm x).property (boundaryFullPowerDegree35Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree35Norm,boundaryFullPowerDegree35Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))))))=(boundaryFullPowerDegree35Block5Norm x).val+(boundaryFullPowerDegree35Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block5Norm x).property (boundaryFullPowerDegree35Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block5Norm,boundaryFullPowerDegree35Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x))))))))=(boundaryFullPowerDegree35Block3Norm x).val+(boundaryFullPowerDegree35Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block3Norm x).property (boundaryFullPowerDegree35Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block3Norm,boundaryFullPowerDegree35Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x))=c} := by

  have he : ((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x))=(boundaryRePowerRow77_12Degree35Norm x).val+(boundaryRePowerRow77_13Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree35Norm x).property (boundaryRePowerRow77_13Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree35Norm,boundaryRePowerRow77_13Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x))))=(boundaryRePowerRow77_11Degree35Norm x).val+(boundaryFullPowerDegree35Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree35Norm x).property (boundaryFullPowerDegree35Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree35Norm,boundaryFullPowerDegree35Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x))=c} := by

  have he : ((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x))=(boundaryRePowerRow77_15Degree35Norm x).val+(boundaryRePowerRow77_16Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree35Norm x).property (boundaryRePowerRow77_16Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree35Norm,boundaryRePowerRow77_16Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x))))=(boundaryRePowerRow77_14Degree35Norm x).val+(boundaryFullPowerDegree35Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree35Norm x).property (boundaryFullPowerDegree35Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree35Norm,boundaryFullPowerDegree35Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x))))))=(boundaryFullPowerDegree35Block11Norm x).val+(boundaryFullPowerDegree35Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block11Norm x).property (boundaryFullPowerDegree35Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block11Norm,boundaryFullPowerDegree35Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x))=c} := by

  have he : ((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x))=(boundaryRePowerRow77_18Degree35Norm x).val+(boundaryRePowerRow77_19Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree35Norm x).property (boundaryRePowerRow77_19Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree35Norm,boundaryRePowerRow77_19Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x))))=(boundaryRePowerRow77_17Degree35Norm x).val+(boundaryFullPowerDegree35Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree35Norm x).property (boundaryFullPowerDegree35Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree35Norm,boundaryFullPowerDegree35Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))=c} := by

  have he : ((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))=(boundaryRePowerRow77_21Degree35Norm x).val+(boundaryRePowerRow77_22Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree35Norm x).property (boundaryRePowerRow77_22Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree35Norm,boundaryRePowerRow77_22Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))=(boundaryRePowerRow77_20Degree35Norm x).val+(boundaryFullPowerDegree35Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree35Norm x).property (boundaryFullPowerDegree35Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree35Norm,boundaryFullPowerDegree35Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))))=(boundaryFullPowerDegree35Block16Norm x).val+(boundaryFullPowerDegree35Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block16Norm x).property (boundaryFullPowerDegree35Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block16Norm,boundaryFullPowerDegree35Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))))))=(boundaryFullPowerDegree35Block14Norm x).val+(boundaryFullPowerDegree35Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block14Norm x).property (boundaryFullPowerDegree35Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block14Norm,boundaryFullPowerDegree35Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x)))))))))+(((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x)))))))))+(((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x))))))))))=(boundaryFullPowerDegree35Block9Norm x).val+(boundaryFullPowerDegree35Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block9Norm x).property (boundaryFullPowerDegree35Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block9Norm,boundaryFullPowerDegree35Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x))=c} := by

  have he : ((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x))=(boundaryImPowerRow77_0Degree35Norm x).val+(boundaryImPowerRow77_1Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree35Norm x).property (boundaryImPowerRow77_1Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree35Norm,boundaryImPowerRow77_1Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x))=c} := by

  have he : ((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x))=(boundaryImPowerRow77_3Degree35Norm x).val+(boundaryImPowerRow77_4Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree35Norm x).property (boundaryImPowerRow77_4Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree35Norm,boundaryImPowerRow77_4Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x))))=(boundaryImPowerRow77_2Degree35Norm x).val+(boundaryFullPowerDegree35Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree35Norm x).property (boundaryFullPowerDegree35Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree35Norm,boundaryFullPowerDegree35Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x))))))=(boundaryFullPowerDegree35Block22Norm x).val+(boundaryFullPowerDegree35Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block22Norm x).property (boundaryFullPowerDegree35Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block22Norm,boundaryFullPowerDegree35Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x))=c} := by

  have he : ((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x))=(boundaryImPowerRow77_6Degree35Norm x).val+(boundaryImPowerRow77_7Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree35Norm x).property (boundaryImPowerRow77_7Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree35Norm,boundaryImPowerRow77_7Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x))))=(boundaryImPowerRow77_5Degree35Norm x).val+(boundaryFullPowerDegree35Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree35Norm x).property (boundaryFullPowerDegree35Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree35Norm,boundaryFullPowerDegree35Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))=c} := by

  have he : ((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))=(boundaryImPowerRow77_9Degree35Norm x).val+(boundaryImPowerRow77_10Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree35Norm x).property (boundaryImPowerRow77_10Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree35Norm,boundaryImPowerRow77_10Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))))=(boundaryImPowerRow77_8Degree35Norm x).val+(boundaryFullPowerDegree35Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree35Norm x).property (boundaryFullPowerDegree35Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree35Norm,boundaryFullPowerDegree35Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))))))=(boundaryFullPowerDegree35Block27Norm x).val+(boundaryFullPowerDegree35Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block27Norm x).property (boundaryFullPowerDegree35Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block27Norm,boundaryFullPowerDegree35Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x))))))))=(boundaryFullPowerDegree35Block25Norm x).val+(boundaryFullPowerDegree35Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block25Norm x).property (boundaryFullPowerDegree35Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block25Norm,boundaryFullPowerDegree35Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x))=c} := by

  have he : ((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x))=(boundaryImPowerRow77_12Degree35Norm x).val+(boundaryImPowerRow77_13Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree35Norm x).property (boundaryImPowerRow77_13Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree35Norm,boundaryImPowerRow77_13Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x))))=(boundaryImPowerRow77_11Degree35Norm x).val+(boundaryFullPowerDegree35Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree35Norm x).property (boundaryFullPowerDegree35Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree35Norm,boundaryFullPowerDegree35Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x))=c} := by

  have he : ((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x))=(boundaryImPowerRow77_15Degree35Norm x).val+(boundaryImPowerRow77_16Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree35Norm x).property (boundaryImPowerRow77_16Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree35Norm,boundaryImPowerRow77_16Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x))))=(boundaryImPowerRow77_14Degree35Norm x).val+(boundaryFullPowerDegree35Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree35Norm x).property (boundaryFullPowerDegree35Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree35Norm,boundaryFullPowerDegree35Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x))))))=(boundaryFullPowerDegree35Block33Norm x).val+(boundaryFullPowerDegree35Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block33Norm x).property (boundaryFullPowerDegree35Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block33Norm,boundaryFullPowerDegree35Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x))=c} := by

  have he : ((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x))=(boundaryImPowerRow77_18Degree35Norm x).val+(boundaryImPowerRow77_19Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree35Norm x).property (boundaryImPowerRow77_19Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree35Norm,boundaryImPowerRow77_19Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x))))=(boundaryImPowerRow77_17Degree35Norm x).val+(boundaryFullPowerDegree35Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree35Norm x).property (boundaryFullPowerDegree35Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree35Norm,boundaryFullPowerDegree35Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))=c} := by

  have he : ((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))=(boundaryImPowerRow77_21Degree35Norm x).val+(boundaryLowPowerRow77Degree35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree35Norm x).property (boundaryLowPowerRow77Degree35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree35Norm,boundaryLowPowerRow77Degree35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))=(boundaryImPowerRow77_20Degree35Norm x).val+(boundaryFullPowerDegree35Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree35Norm x).property (boundaryFullPowerDegree35Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree35Norm,boundaryFullPowerDegree35Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))=(boundaryFullPowerDegree35Block38Norm x).val+(boundaryFullPowerDegree35Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block38Norm x).property (boundaryFullPowerDegree35Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block38Norm,boundaryFullPowerDegree35Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))))=(boundaryFullPowerDegree35Block36Norm x).val+(boundaryFullPowerDegree35Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block36Norm x).property (boundaryFullPowerDegree35Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block36Norm,boundaryFullPowerDegree35Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x)))))))))+(((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x)))))))))+(((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))))))=(boundaryFullPowerDegree35Block31Norm x).val+(boundaryFullPowerDegree35Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block31Norm x).property (boundaryFullPowerDegree35Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block31Norm,boundaryFullPowerDegree35Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree35Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x)))))))))+(((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x)))))))))))+(((((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x)))))))))+(((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x)))))))))+(((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x)))))))))))+(((((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x)))))))))+(((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x))))))))))))=(boundaryFullPowerDegree35Block21Norm x).val+(boundaryFullPowerDegree35Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree35Block21Norm x).property (boundaryFullPowerDegree35Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block21Norm,boundaryFullPowerDegree35Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree35Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 35 x=c} := by

  have he0 : boundaryFullPowerRow77 35 x=((((((((((boundaryRePowerRow77_0 35 x)+(boundaryRePowerRow77_1 35 x)))+(((boundaryRePowerRow77_2 35 x)+(((boundaryRePowerRow77_3 35 x)+(boundaryRePowerRow77_4 35 x)))))))+(((((boundaryRePowerRow77_5 35 x)+(((boundaryRePowerRow77_6 35 x)+(boundaryRePowerRow77_7 35 x)))))+(((boundaryRePowerRow77_8 35 x)+(((boundaryRePowerRow77_9 35 x)+(boundaryRePowerRow77_10 35 x)))))))))+(((((((boundaryRePowerRow77_11 35 x)+(((boundaryRePowerRow77_12 35 x)+(boundaryRePowerRow77_13 35 x)))))+(((boundaryRePowerRow77_14 35 x)+(((boundaryRePowerRow77_15 35 x)+(boundaryRePowerRow77_16 35 x)))))))+(((((boundaryRePowerRow77_17 35 x)+(((boundaryRePowerRow77_18 35 x)+(boundaryRePowerRow77_19 35 x)))))+(((boundaryRePowerRow77_20 35 x)+(((boundaryRePowerRow77_21 35 x)+(boundaryRePowerRow77_22 35 x)))))))))))+(((((((((boundaryImPowerRow77_0 35 x)+(boundaryImPowerRow77_1 35 x)))+(((boundaryImPowerRow77_2 35 x)+(((boundaryImPowerRow77_3 35 x)+(boundaryImPowerRow77_4 35 x)))))))+(((((boundaryImPowerRow77_5 35 x)+(((boundaryImPowerRow77_6 35 x)+(boundaryImPowerRow77_7 35 x)))))+(((boundaryImPowerRow77_8 35 x)+(((boundaryImPowerRow77_9 35 x)+(boundaryImPowerRow77_10 35 x)))))))))+(((((((boundaryImPowerRow77_11 35 x)+(((boundaryImPowerRow77_12 35 x)+(boundaryImPowerRow77_13 35 x)))))+(((boundaryImPowerRow77_14 35 x)+(((boundaryImPowerRow77_15 35 x)+(boundaryImPowerRow77_16 35 x)))))))+(((((boundaryImPowerRow77_17 35 x)+(((boundaryImPowerRow77_18 35 x)+(boundaryImPowerRow77_19 35 x)))))+(((boundaryImPowerRow77_20 35 x)+(((boundaryImPowerRow77_21 35 x)+(boundaryLowPowerRow77 35 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree35Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree35Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
