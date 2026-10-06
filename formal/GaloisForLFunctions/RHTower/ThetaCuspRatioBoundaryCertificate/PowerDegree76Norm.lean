import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree76Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree76Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x))=c} := by

  have he : ((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x))=(boundaryRePowerRow77_0Degree76Norm x).val+(boundaryRePowerRow77_1Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree76Norm x).property (boundaryRePowerRow77_1Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree76Norm,boundaryRePowerRow77_1Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x))=c} := by

  have he : ((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x))=(boundaryRePowerRow77_3Degree76Norm x).val+(boundaryRePowerRow77_4Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree76Norm x).property (boundaryRePowerRow77_4Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree76Norm,boundaryRePowerRow77_4Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x))))=(boundaryRePowerRow77_2Degree76Norm x).val+(boundaryFullPowerDegree76Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree76Norm x).property (boundaryFullPowerDegree76Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree76Norm,boundaryFullPowerDegree76Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x))))))=(boundaryFullPowerDegree76Block0Norm x).val+(boundaryFullPowerDegree76Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block0Norm x).property (boundaryFullPowerDegree76Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block0Norm,boundaryFullPowerDegree76Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x))=c} := by

  have he : ((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x))=(boundaryRePowerRow77_6Degree76Norm x).val+(boundaryRePowerRow77_7Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree76Norm x).property (boundaryRePowerRow77_7Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree76Norm,boundaryRePowerRow77_7Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x))))=(boundaryRePowerRow77_5Degree76Norm x).val+(boundaryFullPowerDegree76Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree76Norm x).property (boundaryFullPowerDegree76Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree76Norm,boundaryFullPowerDegree76Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))=c} := by

  have he : ((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))=(boundaryRePowerRow77_9Degree76Norm x).val+(boundaryRePowerRow77_10Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree76Norm x).property (boundaryRePowerRow77_10Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree76Norm,boundaryRePowerRow77_10Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))))=(boundaryRePowerRow77_8Degree76Norm x).val+(boundaryFullPowerDegree76Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree76Norm x).property (boundaryFullPowerDegree76Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree76Norm,boundaryFullPowerDegree76Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))))))=(boundaryFullPowerDegree76Block5Norm x).val+(boundaryFullPowerDegree76Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block5Norm x).property (boundaryFullPowerDegree76Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block5Norm,boundaryFullPowerDegree76Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x))))))))=(boundaryFullPowerDegree76Block3Norm x).val+(boundaryFullPowerDegree76Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block3Norm x).property (boundaryFullPowerDegree76Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block3Norm,boundaryFullPowerDegree76Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x))=c} := by

  have he : ((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x))=(boundaryRePowerRow77_12Degree76Norm x).val+(boundaryRePowerRow77_13Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree76Norm x).property (boundaryRePowerRow77_13Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree76Norm,boundaryRePowerRow77_13Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x))))=(boundaryRePowerRow77_11Degree76Norm x).val+(boundaryFullPowerDegree76Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree76Norm x).property (boundaryFullPowerDegree76Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree76Norm,boundaryFullPowerDegree76Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x))=c} := by

  have he : ((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x))=(boundaryRePowerRow77_15Degree76Norm x).val+(boundaryRePowerRow77_16Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree76Norm x).property (boundaryRePowerRow77_16Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree76Norm,boundaryRePowerRow77_16Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x))))=(boundaryRePowerRow77_14Degree76Norm x).val+(boundaryFullPowerDegree76Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree76Norm x).property (boundaryFullPowerDegree76Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree76Norm,boundaryFullPowerDegree76Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x))))))=(boundaryFullPowerDegree76Block11Norm x).val+(boundaryFullPowerDegree76Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block11Norm x).property (boundaryFullPowerDegree76Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block11Norm,boundaryFullPowerDegree76Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x))=c} := by

  have he : ((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x))=(boundaryRePowerRow77_18Degree76Norm x).val+(boundaryRePowerRow77_19Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree76Norm x).property (boundaryRePowerRow77_19Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree76Norm,boundaryRePowerRow77_19Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x))))=(boundaryRePowerRow77_17Degree76Norm x).val+(boundaryFullPowerDegree76Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree76Norm x).property (boundaryFullPowerDegree76Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree76Norm,boundaryFullPowerDegree76Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))=c} := by

  have he : ((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))=(boundaryRePowerRow77_21Degree76Norm x).val+(boundaryRePowerRow77_22Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree76Norm x).property (boundaryRePowerRow77_22Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree76Norm,boundaryRePowerRow77_22Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))=(boundaryRePowerRow77_20Degree76Norm x).val+(boundaryFullPowerDegree76Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree76Norm x).property (boundaryFullPowerDegree76Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree76Norm,boundaryFullPowerDegree76Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))))=(boundaryFullPowerDegree76Block16Norm x).val+(boundaryFullPowerDegree76Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block16Norm x).property (boundaryFullPowerDegree76Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block16Norm,boundaryFullPowerDegree76Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))))))=(boundaryFullPowerDegree76Block14Norm x).val+(boundaryFullPowerDegree76Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block14Norm x).property (boundaryFullPowerDegree76Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block14Norm,boundaryFullPowerDegree76Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x)))))))))+(((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x)))))))))+(((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x))))))))))=(boundaryFullPowerDegree76Block9Norm x).val+(boundaryFullPowerDegree76Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block9Norm x).property (boundaryFullPowerDegree76Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block9Norm,boundaryFullPowerDegree76Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x))=c} := by

  have he : ((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x))=(boundaryImPowerRow77_0Degree76Norm x).val+(boundaryImPowerRow77_1Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree76Norm x).property (boundaryImPowerRow77_1Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree76Norm,boundaryImPowerRow77_1Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x))=c} := by

  have he : ((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x))=(boundaryImPowerRow77_3Degree76Norm x).val+(boundaryImPowerRow77_4Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree76Norm x).property (boundaryImPowerRow77_4Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree76Norm,boundaryImPowerRow77_4Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x))))=(boundaryImPowerRow77_2Degree76Norm x).val+(boundaryFullPowerDegree76Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree76Norm x).property (boundaryFullPowerDegree76Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree76Norm,boundaryFullPowerDegree76Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x))))))=(boundaryFullPowerDegree76Block22Norm x).val+(boundaryFullPowerDegree76Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block22Norm x).property (boundaryFullPowerDegree76Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block22Norm,boundaryFullPowerDegree76Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x))=c} := by

  have he : ((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x))=(boundaryImPowerRow77_6Degree76Norm x).val+(boundaryImPowerRow77_7Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree76Norm x).property (boundaryImPowerRow77_7Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree76Norm,boundaryImPowerRow77_7Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x))))=(boundaryImPowerRow77_5Degree76Norm x).val+(boundaryFullPowerDegree76Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree76Norm x).property (boundaryFullPowerDegree76Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree76Norm,boundaryFullPowerDegree76Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))=c} := by

  have he : ((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))=(boundaryImPowerRow77_9Degree76Norm x).val+(boundaryImPowerRow77_10Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree76Norm x).property (boundaryImPowerRow77_10Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree76Norm,boundaryImPowerRow77_10Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))))=(boundaryImPowerRow77_8Degree76Norm x).val+(boundaryFullPowerDegree76Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree76Norm x).property (boundaryFullPowerDegree76Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree76Norm,boundaryFullPowerDegree76Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))))))=(boundaryFullPowerDegree76Block27Norm x).val+(boundaryFullPowerDegree76Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block27Norm x).property (boundaryFullPowerDegree76Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block27Norm,boundaryFullPowerDegree76Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x))))))))=(boundaryFullPowerDegree76Block25Norm x).val+(boundaryFullPowerDegree76Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block25Norm x).property (boundaryFullPowerDegree76Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block25Norm,boundaryFullPowerDegree76Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x))=c} := by

  have he : ((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x))=(boundaryImPowerRow77_12Degree76Norm x).val+(boundaryImPowerRow77_13Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree76Norm x).property (boundaryImPowerRow77_13Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree76Norm,boundaryImPowerRow77_13Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x))))=(boundaryImPowerRow77_11Degree76Norm x).val+(boundaryFullPowerDegree76Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree76Norm x).property (boundaryFullPowerDegree76Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree76Norm,boundaryFullPowerDegree76Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x))=c} := by

  have he : ((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x))=(boundaryImPowerRow77_15Degree76Norm x).val+(boundaryImPowerRow77_16Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree76Norm x).property (boundaryImPowerRow77_16Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree76Norm,boundaryImPowerRow77_16Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x))))=(boundaryImPowerRow77_14Degree76Norm x).val+(boundaryFullPowerDegree76Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree76Norm x).property (boundaryFullPowerDegree76Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree76Norm,boundaryFullPowerDegree76Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x))))))=(boundaryFullPowerDegree76Block33Norm x).val+(boundaryFullPowerDegree76Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block33Norm x).property (boundaryFullPowerDegree76Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block33Norm,boundaryFullPowerDegree76Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x))=c} := by

  have he : ((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x))=(boundaryImPowerRow77_18Degree76Norm x).val+(boundaryImPowerRow77_19Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree76Norm x).property (boundaryImPowerRow77_19Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree76Norm,boundaryImPowerRow77_19Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x))))=(boundaryImPowerRow77_17Degree76Norm x).val+(boundaryFullPowerDegree76Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree76Norm x).property (boundaryFullPowerDegree76Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree76Norm,boundaryFullPowerDegree76Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))=c} := by

  have he : ((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))=(boundaryImPowerRow77_21Degree76Norm x).val+(boundaryLowPowerRow77Degree76Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree76Norm x).property (boundaryLowPowerRow77Degree76Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree76Norm,boundaryLowPowerRow77Degree76Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))=(boundaryImPowerRow77_20Degree76Norm x).val+(boundaryFullPowerDegree76Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree76Norm x).property (boundaryFullPowerDegree76Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree76Norm,boundaryFullPowerDegree76Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))=(boundaryFullPowerDegree76Block38Norm x).val+(boundaryFullPowerDegree76Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block38Norm x).property (boundaryFullPowerDegree76Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block38Norm,boundaryFullPowerDegree76Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))))=(boundaryFullPowerDegree76Block36Norm x).val+(boundaryFullPowerDegree76Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block36Norm x).property (boundaryFullPowerDegree76Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block36Norm,boundaryFullPowerDegree76Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x)))))))))+(((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x)))))))))+(((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))))))=(boundaryFullPowerDegree76Block31Norm x).val+(boundaryFullPowerDegree76Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block31Norm x).property (boundaryFullPowerDegree76Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block31Norm,boundaryFullPowerDegree76Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree76Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x)))))))))+(((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x)))))))))))+(((((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x)))))))))+(((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x)))))))))+(((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x)))))))))))+(((((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x)))))))))+(((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x))))))))))))=(boundaryFullPowerDegree76Block21Norm x).val+(boundaryFullPowerDegree76Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree76Block21Norm x).property (boundaryFullPowerDegree76Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block21Norm,boundaryFullPowerDegree76Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree76Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 76 x=c} := by

  have he0 : boundaryFullPowerRow77 76 x=((((((((((boundaryRePowerRow77_0 76 x)+(boundaryRePowerRow77_1 76 x)))+(((boundaryRePowerRow77_2 76 x)+(((boundaryRePowerRow77_3 76 x)+(boundaryRePowerRow77_4 76 x)))))))+(((((boundaryRePowerRow77_5 76 x)+(((boundaryRePowerRow77_6 76 x)+(boundaryRePowerRow77_7 76 x)))))+(((boundaryRePowerRow77_8 76 x)+(((boundaryRePowerRow77_9 76 x)+(boundaryRePowerRow77_10 76 x)))))))))+(((((((boundaryRePowerRow77_11 76 x)+(((boundaryRePowerRow77_12 76 x)+(boundaryRePowerRow77_13 76 x)))))+(((boundaryRePowerRow77_14 76 x)+(((boundaryRePowerRow77_15 76 x)+(boundaryRePowerRow77_16 76 x)))))))+(((((boundaryRePowerRow77_17 76 x)+(((boundaryRePowerRow77_18 76 x)+(boundaryRePowerRow77_19 76 x)))))+(((boundaryRePowerRow77_20 76 x)+(((boundaryRePowerRow77_21 76 x)+(boundaryRePowerRow77_22 76 x)))))))))))+(((((((((boundaryImPowerRow77_0 76 x)+(boundaryImPowerRow77_1 76 x)))+(((boundaryImPowerRow77_2 76 x)+(((boundaryImPowerRow77_3 76 x)+(boundaryImPowerRow77_4 76 x)))))))+(((((boundaryImPowerRow77_5 76 x)+(((boundaryImPowerRow77_6 76 x)+(boundaryImPowerRow77_7 76 x)))))+(((boundaryImPowerRow77_8 76 x)+(((boundaryImPowerRow77_9 76 x)+(boundaryImPowerRow77_10 76 x)))))))))+(((((((boundaryImPowerRow77_11 76 x)+(((boundaryImPowerRow77_12 76 x)+(boundaryImPowerRow77_13 76 x)))))+(((boundaryImPowerRow77_14 76 x)+(((boundaryImPowerRow77_15 76 x)+(boundaryImPowerRow77_16 76 x)))))))+(((((boundaryImPowerRow77_17 76 x)+(((boundaryImPowerRow77_18 76 x)+(boundaryImPowerRow77_19 76 x)))))+(((boundaryImPowerRow77_20 76 x)+(((boundaryImPowerRow77_21 76 x)+(boundaryLowPowerRow77 76 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree76Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree76Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
