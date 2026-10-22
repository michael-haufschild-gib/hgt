import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree87Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree87Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x))=c} := by

  have he : ((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x))=(boundaryRePowerRow77_0Degree87Norm x).val+(boundaryRePowerRow77_1Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree87Norm x).property (boundaryRePowerRow77_1Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree87Norm,boundaryRePowerRow77_1Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x))=c} := by

  have he : ((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x))=(boundaryRePowerRow77_3Degree87Norm x).val+(boundaryRePowerRow77_4Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree87Norm x).property (boundaryRePowerRow77_4Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree87Norm,boundaryRePowerRow77_4Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x))))=(boundaryRePowerRow77_2Degree87Norm x).val+(boundaryFullPowerDegree87Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree87Norm x).property (boundaryFullPowerDegree87Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree87Norm,boundaryFullPowerDegree87Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x))))))=(boundaryFullPowerDegree87Block0Norm x).val+(boundaryFullPowerDegree87Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block0Norm x).property (boundaryFullPowerDegree87Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block0Norm,boundaryFullPowerDegree87Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x))=c} := by

  have he : ((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x))=(boundaryRePowerRow77_6Degree87Norm x).val+(boundaryRePowerRow77_7Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree87Norm x).property (boundaryRePowerRow77_7Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree87Norm,boundaryRePowerRow77_7Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x))))=(boundaryRePowerRow77_5Degree87Norm x).val+(boundaryFullPowerDegree87Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree87Norm x).property (boundaryFullPowerDegree87Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree87Norm,boundaryFullPowerDegree87Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))=c} := by

  have he : ((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))=(boundaryRePowerRow77_9Degree87Norm x).val+(boundaryRePowerRow77_10Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree87Norm x).property (boundaryRePowerRow77_10Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree87Norm,boundaryRePowerRow77_10Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))))=(boundaryRePowerRow77_8Degree87Norm x).val+(boundaryFullPowerDegree87Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree87Norm x).property (boundaryFullPowerDegree87Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree87Norm,boundaryFullPowerDegree87Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))))))=(boundaryFullPowerDegree87Block5Norm x).val+(boundaryFullPowerDegree87Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block5Norm x).property (boundaryFullPowerDegree87Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block5Norm,boundaryFullPowerDegree87Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x))))))))=(boundaryFullPowerDegree87Block3Norm x).val+(boundaryFullPowerDegree87Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block3Norm x).property (boundaryFullPowerDegree87Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block3Norm,boundaryFullPowerDegree87Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x))=c} := by

  have he : ((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x))=(boundaryRePowerRow77_12Degree87Norm x).val+(boundaryRePowerRow77_13Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree87Norm x).property (boundaryRePowerRow77_13Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree87Norm,boundaryRePowerRow77_13Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x))))=(boundaryRePowerRow77_11Degree87Norm x).val+(boundaryFullPowerDegree87Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree87Norm x).property (boundaryFullPowerDegree87Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree87Norm,boundaryFullPowerDegree87Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x))=c} := by

  have he : ((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x))=(boundaryRePowerRow77_15Degree87Norm x).val+(boundaryRePowerRow77_16Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree87Norm x).property (boundaryRePowerRow77_16Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree87Norm,boundaryRePowerRow77_16Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x))))=(boundaryRePowerRow77_14Degree87Norm x).val+(boundaryFullPowerDegree87Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree87Norm x).property (boundaryFullPowerDegree87Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree87Norm,boundaryFullPowerDegree87Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x))))))=(boundaryFullPowerDegree87Block11Norm x).val+(boundaryFullPowerDegree87Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block11Norm x).property (boundaryFullPowerDegree87Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block11Norm,boundaryFullPowerDegree87Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x))=c} := by

  have he : ((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x))=(boundaryRePowerRow77_18Degree87Norm x).val+(boundaryRePowerRow77_19Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree87Norm x).property (boundaryRePowerRow77_19Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree87Norm,boundaryRePowerRow77_19Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x))))=(boundaryRePowerRow77_17Degree87Norm x).val+(boundaryFullPowerDegree87Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree87Norm x).property (boundaryFullPowerDegree87Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree87Norm,boundaryFullPowerDegree87Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))=c} := by

  have he : ((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))=(boundaryRePowerRow77_21Degree87Norm x).val+(boundaryRePowerRow77_22Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree87Norm x).property (boundaryRePowerRow77_22Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree87Norm,boundaryRePowerRow77_22Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))=(boundaryRePowerRow77_20Degree87Norm x).val+(boundaryFullPowerDegree87Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree87Norm x).property (boundaryFullPowerDegree87Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree87Norm,boundaryFullPowerDegree87Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))))=(boundaryFullPowerDegree87Block16Norm x).val+(boundaryFullPowerDegree87Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block16Norm x).property (boundaryFullPowerDegree87Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block16Norm,boundaryFullPowerDegree87Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))))))=(boundaryFullPowerDegree87Block14Norm x).val+(boundaryFullPowerDegree87Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block14Norm x).property (boundaryFullPowerDegree87Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block14Norm,boundaryFullPowerDegree87Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x)))))))))+(((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x)))))))))+(((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x))))))))))=(boundaryFullPowerDegree87Block9Norm x).val+(boundaryFullPowerDegree87Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block9Norm x).property (boundaryFullPowerDegree87Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block9Norm,boundaryFullPowerDegree87Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x))=c} := by

  have he : ((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x))=(boundaryImPowerRow77_0Degree87Norm x).val+(boundaryImPowerRow77_1Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree87Norm x).property (boundaryImPowerRow77_1Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree87Norm,boundaryImPowerRow77_1Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x))=c} := by

  have he : ((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x))=(boundaryImPowerRow77_3Degree87Norm x).val+(boundaryImPowerRow77_4Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree87Norm x).property (boundaryImPowerRow77_4Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree87Norm,boundaryImPowerRow77_4Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x))))=(boundaryImPowerRow77_2Degree87Norm x).val+(boundaryFullPowerDegree87Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree87Norm x).property (boundaryFullPowerDegree87Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree87Norm,boundaryFullPowerDegree87Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x))))))=(boundaryFullPowerDegree87Block22Norm x).val+(boundaryFullPowerDegree87Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block22Norm x).property (boundaryFullPowerDegree87Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block22Norm,boundaryFullPowerDegree87Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x))=c} := by

  have he : ((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x))=(boundaryImPowerRow77_6Degree87Norm x).val+(boundaryImPowerRow77_7Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree87Norm x).property (boundaryImPowerRow77_7Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree87Norm,boundaryImPowerRow77_7Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x))))=(boundaryImPowerRow77_5Degree87Norm x).val+(boundaryFullPowerDegree87Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree87Norm x).property (boundaryFullPowerDegree87Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree87Norm,boundaryFullPowerDegree87Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))=c} := by

  have he : ((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))=(boundaryImPowerRow77_9Degree87Norm x).val+(boundaryImPowerRow77_10Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree87Norm x).property (boundaryImPowerRow77_10Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree87Norm,boundaryImPowerRow77_10Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))))=(boundaryImPowerRow77_8Degree87Norm x).val+(boundaryFullPowerDegree87Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree87Norm x).property (boundaryFullPowerDegree87Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree87Norm,boundaryFullPowerDegree87Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))))))=(boundaryFullPowerDegree87Block27Norm x).val+(boundaryFullPowerDegree87Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block27Norm x).property (boundaryFullPowerDegree87Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block27Norm,boundaryFullPowerDegree87Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x))))))))=(boundaryFullPowerDegree87Block25Norm x).val+(boundaryFullPowerDegree87Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block25Norm x).property (boundaryFullPowerDegree87Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block25Norm,boundaryFullPowerDegree87Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x))=c} := by

  have he : ((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x))=(boundaryImPowerRow77_12Degree87Norm x).val+(boundaryImPowerRow77_13Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree87Norm x).property (boundaryImPowerRow77_13Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree87Norm,boundaryImPowerRow77_13Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x))))=(boundaryImPowerRow77_11Degree87Norm x).val+(boundaryFullPowerDegree87Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree87Norm x).property (boundaryFullPowerDegree87Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree87Norm,boundaryFullPowerDegree87Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x))=c} := by

  have he : ((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x))=(boundaryImPowerRow77_15Degree87Norm x).val+(boundaryImPowerRow77_16Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree87Norm x).property (boundaryImPowerRow77_16Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree87Norm,boundaryImPowerRow77_16Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x))))=(boundaryImPowerRow77_14Degree87Norm x).val+(boundaryFullPowerDegree87Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree87Norm x).property (boundaryFullPowerDegree87Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree87Norm,boundaryFullPowerDegree87Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x))))))=(boundaryFullPowerDegree87Block33Norm x).val+(boundaryFullPowerDegree87Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block33Norm x).property (boundaryFullPowerDegree87Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block33Norm,boundaryFullPowerDegree87Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x))=c} := by

  have he : ((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x))=(boundaryImPowerRow77_18Degree87Norm x).val+(boundaryImPowerRow77_19Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree87Norm x).property (boundaryImPowerRow77_19Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree87Norm,boundaryImPowerRow77_19Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x))))=(boundaryImPowerRow77_17Degree87Norm x).val+(boundaryFullPowerDegree87Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree87Norm x).property (boundaryFullPowerDegree87Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree87Norm,boundaryFullPowerDegree87Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))=c} := by

  have he : ((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))=(boundaryImPowerRow77_21Degree87Norm x).val+(boundaryLowPowerRow77Degree87Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree87Norm x).property (boundaryLowPowerRow77Degree87Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree87Norm,boundaryLowPowerRow77Degree87Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))=(boundaryImPowerRow77_20Degree87Norm x).val+(boundaryFullPowerDegree87Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree87Norm x).property (boundaryFullPowerDegree87Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree87Norm,boundaryFullPowerDegree87Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))=(boundaryFullPowerDegree87Block38Norm x).val+(boundaryFullPowerDegree87Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block38Norm x).property (boundaryFullPowerDegree87Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block38Norm,boundaryFullPowerDegree87Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))))=(boundaryFullPowerDegree87Block36Norm x).val+(boundaryFullPowerDegree87Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block36Norm x).property (boundaryFullPowerDegree87Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block36Norm,boundaryFullPowerDegree87Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x)))))))))+(((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x)))))))))+(((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))))))=(boundaryFullPowerDegree87Block31Norm x).val+(boundaryFullPowerDegree87Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block31Norm x).property (boundaryFullPowerDegree87Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block31Norm,boundaryFullPowerDegree87Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree87Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x)))))))))+(((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x)))))))))))+(((((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x)))))))))+(((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x)))))))))+(((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x)))))))))))+(((((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x)))))))))+(((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x))))))))))))=(boundaryFullPowerDegree87Block21Norm x).val+(boundaryFullPowerDegree87Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree87Block21Norm x).property (boundaryFullPowerDegree87Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block21Norm,boundaryFullPowerDegree87Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree87Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 87 x=c} := by

  have he0 : boundaryFullPowerRow77 87 x=((((((((((boundaryRePowerRow77_0 87 x)+(boundaryRePowerRow77_1 87 x)))+(((boundaryRePowerRow77_2 87 x)+(((boundaryRePowerRow77_3 87 x)+(boundaryRePowerRow77_4 87 x)))))))+(((((boundaryRePowerRow77_5 87 x)+(((boundaryRePowerRow77_6 87 x)+(boundaryRePowerRow77_7 87 x)))))+(((boundaryRePowerRow77_8 87 x)+(((boundaryRePowerRow77_9 87 x)+(boundaryRePowerRow77_10 87 x)))))))))+(((((((boundaryRePowerRow77_11 87 x)+(((boundaryRePowerRow77_12 87 x)+(boundaryRePowerRow77_13 87 x)))))+(((boundaryRePowerRow77_14 87 x)+(((boundaryRePowerRow77_15 87 x)+(boundaryRePowerRow77_16 87 x)))))))+(((((boundaryRePowerRow77_17 87 x)+(((boundaryRePowerRow77_18 87 x)+(boundaryRePowerRow77_19 87 x)))))+(((boundaryRePowerRow77_20 87 x)+(((boundaryRePowerRow77_21 87 x)+(boundaryRePowerRow77_22 87 x)))))))))))+(((((((((boundaryImPowerRow77_0 87 x)+(boundaryImPowerRow77_1 87 x)))+(((boundaryImPowerRow77_2 87 x)+(((boundaryImPowerRow77_3 87 x)+(boundaryImPowerRow77_4 87 x)))))))+(((((boundaryImPowerRow77_5 87 x)+(((boundaryImPowerRow77_6 87 x)+(boundaryImPowerRow77_7 87 x)))))+(((boundaryImPowerRow77_8 87 x)+(((boundaryImPowerRow77_9 87 x)+(boundaryImPowerRow77_10 87 x)))))))))+(((((((boundaryImPowerRow77_11 87 x)+(((boundaryImPowerRow77_12 87 x)+(boundaryImPowerRow77_13 87 x)))))+(((boundaryImPowerRow77_14 87 x)+(((boundaryImPowerRow77_15 87 x)+(boundaryImPowerRow77_16 87 x)))))))+(((((boundaryImPowerRow77_17 87 x)+(((boundaryImPowerRow77_18 87 x)+(boundaryImPowerRow77_19 87 x)))))+(((boundaryImPowerRow77_20 87 x)+(((boundaryImPowerRow77_21 87 x)+(boundaryLowPowerRow77 87 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree87Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree87Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
