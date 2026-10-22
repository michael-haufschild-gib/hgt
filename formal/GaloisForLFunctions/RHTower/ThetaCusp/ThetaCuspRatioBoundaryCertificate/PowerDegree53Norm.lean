import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree53Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree53Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x))=c} := by

  have he : ((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x))=(boundaryRePowerRow77_0Degree53Norm x).val+(boundaryRePowerRow77_1Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree53Norm x).property (boundaryRePowerRow77_1Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree53Norm,boundaryRePowerRow77_1Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x))=c} := by

  have he : ((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x))=(boundaryRePowerRow77_3Degree53Norm x).val+(boundaryRePowerRow77_4Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree53Norm x).property (boundaryRePowerRow77_4Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree53Norm,boundaryRePowerRow77_4Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x))))=(boundaryRePowerRow77_2Degree53Norm x).val+(boundaryFullPowerDegree53Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree53Norm x).property (boundaryFullPowerDegree53Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree53Norm,boundaryFullPowerDegree53Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x))))))=(boundaryFullPowerDegree53Block0Norm x).val+(boundaryFullPowerDegree53Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block0Norm x).property (boundaryFullPowerDegree53Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block0Norm,boundaryFullPowerDegree53Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x))=c} := by

  have he : ((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x))=(boundaryRePowerRow77_6Degree53Norm x).val+(boundaryRePowerRow77_7Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree53Norm x).property (boundaryRePowerRow77_7Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree53Norm,boundaryRePowerRow77_7Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x))))=(boundaryRePowerRow77_5Degree53Norm x).val+(boundaryFullPowerDegree53Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree53Norm x).property (boundaryFullPowerDegree53Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree53Norm,boundaryFullPowerDegree53Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))=c} := by

  have he : ((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))=(boundaryRePowerRow77_9Degree53Norm x).val+(boundaryRePowerRow77_10Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree53Norm x).property (boundaryRePowerRow77_10Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree53Norm,boundaryRePowerRow77_10Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))))=(boundaryRePowerRow77_8Degree53Norm x).val+(boundaryFullPowerDegree53Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree53Norm x).property (boundaryFullPowerDegree53Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree53Norm,boundaryFullPowerDegree53Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))))))=(boundaryFullPowerDegree53Block5Norm x).val+(boundaryFullPowerDegree53Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block5Norm x).property (boundaryFullPowerDegree53Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block5Norm,boundaryFullPowerDegree53Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x))))))))=(boundaryFullPowerDegree53Block3Norm x).val+(boundaryFullPowerDegree53Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block3Norm x).property (boundaryFullPowerDegree53Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block3Norm,boundaryFullPowerDegree53Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x))=c} := by

  have he : ((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x))=(boundaryRePowerRow77_12Degree53Norm x).val+(boundaryRePowerRow77_13Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree53Norm x).property (boundaryRePowerRow77_13Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree53Norm,boundaryRePowerRow77_13Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x))))=(boundaryRePowerRow77_11Degree53Norm x).val+(boundaryFullPowerDegree53Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree53Norm x).property (boundaryFullPowerDegree53Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree53Norm,boundaryFullPowerDegree53Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x))=c} := by

  have he : ((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x))=(boundaryRePowerRow77_15Degree53Norm x).val+(boundaryRePowerRow77_16Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree53Norm x).property (boundaryRePowerRow77_16Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree53Norm,boundaryRePowerRow77_16Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x))))=(boundaryRePowerRow77_14Degree53Norm x).val+(boundaryFullPowerDegree53Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree53Norm x).property (boundaryFullPowerDegree53Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree53Norm,boundaryFullPowerDegree53Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x))))))=(boundaryFullPowerDegree53Block11Norm x).val+(boundaryFullPowerDegree53Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block11Norm x).property (boundaryFullPowerDegree53Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block11Norm,boundaryFullPowerDegree53Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x))=c} := by

  have he : ((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x))=(boundaryRePowerRow77_18Degree53Norm x).val+(boundaryRePowerRow77_19Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree53Norm x).property (boundaryRePowerRow77_19Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree53Norm,boundaryRePowerRow77_19Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x))))=(boundaryRePowerRow77_17Degree53Norm x).val+(boundaryFullPowerDegree53Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree53Norm x).property (boundaryFullPowerDegree53Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree53Norm,boundaryFullPowerDegree53Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))=c} := by

  have he : ((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))=(boundaryRePowerRow77_21Degree53Norm x).val+(boundaryRePowerRow77_22Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree53Norm x).property (boundaryRePowerRow77_22Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree53Norm,boundaryRePowerRow77_22Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))=(boundaryRePowerRow77_20Degree53Norm x).val+(boundaryFullPowerDegree53Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree53Norm x).property (boundaryFullPowerDegree53Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree53Norm,boundaryFullPowerDegree53Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))))=(boundaryFullPowerDegree53Block16Norm x).val+(boundaryFullPowerDegree53Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block16Norm x).property (boundaryFullPowerDegree53Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block16Norm,boundaryFullPowerDegree53Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))))))=(boundaryFullPowerDegree53Block14Norm x).val+(boundaryFullPowerDegree53Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block14Norm x).property (boundaryFullPowerDegree53Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block14Norm,boundaryFullPowerDegree53Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x)))))))))+(((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x)))))))))+(((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x))))))))))=(boundaryFullPowerDegree53Block9Norm x).val+(boundaryFullPowerDegree53Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block9Norm x).property (boundaryFullPowerDegree53Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block9Norm,boundaryFullPowerDegree53Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x))=c} := by

  have he : ((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x))=(boundaryImPowerRow77_0Degree53Norm x).val+(boundaryImPowerRow77_1Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree53Norm x).property (boundaryImPowerRow77_1Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree53Norm,boundaryImPowerRow77_1Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x))=c} := by

  have he : ((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x))=(boundaryImPowerRow77_3Degree53Norm x).val+(boundaryImPowerRow77_4Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree53Norm x).property (boundaryImPowerRow77_4Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree53Norm,boundaryImPowerRow77_4Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x))))=(boundaryImPowerRow77_2Degree53Norm x).val+(boundaryFullPowerDegree53Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree53Norm x).property (boundaryFullPowerDegree53Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree53Norm,boundaryFullPowerDegree53Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x))))))=(boundaryFullPowerDegree53Block22Norm x).val+(boundaryFullPowerDegree53Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block22Norm x).property (boundaryFullPowerDegree53Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block22Norm,boundaryFullPowerDegree53Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x))=c} := by

  have he : ((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x))=(boundaryImPowerRow77_6Degree53Norm x).val+(boundaryImPowerRow77_7Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree53Norm x).property (boundaryImPowerRow77_7Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree53Norm,boundaryImPowerRow77_7Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x))))=(boundaryImPowerRow77_5Degree53Norm x).val+(boundaryFullPowerDegree53Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree53Norm x).property (boundaryFullPowerDegree53Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree53Norm,boundaryFullPowerDegree53Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))=c} := by

  have he : ((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))=(boundaryImPowerRow77_9Degree53Norm x).val+(boundaryImPowerRow77_10Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree53Norm x).property (boundaryImPowerRow77_10Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree53Norm,boundaryImPowerRow77_10Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))))=(boundaryImPowerRow77_8Degree53Norm x).val+(boundaryFullPowerDegree53Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree53Norm x).property (boundaryFullPowerDegree53Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree53Norm,boundaryFullPowerDegree53Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))))))=(boundaryFullPowerDegree53Block27Norm x).val+(boundaryFullPowerDegree53Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block27Norm x).property (boundaryFullPowerDegree53Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block27Norm,boundaryFullPowerDegree53Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x))))))))=(boundaryFullPowerDegree53Block25Norm x).val+(boundaryFullPowerDegree53Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block25Norm x).property (boundaryFullPowerDegree53Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block25Norm,boundaryFullPowerDegree53Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x))=c} := by

  have he : ((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x))=(boundaryImPowerRow77_12Degree53Norm x).val+(boundaryImPowerRow77_13Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree53Norm x).property (boundaryImPowerRow77_13Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree53Norm,boundaryImPowerRow77_13Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x))))=(boundaryImPowerRow77_11Degree53Norm x).val+(boundaryFullPowerDegree53Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree53Norm x).property (boundaryFullPowerDegree53Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree53Norm,boundaryFullPowerDegree53Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x))=c} := by

  have he : ((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x))=(boundaryImPowerRow77_15Degree53Norm x).val+(boundaryImPowerRow77_16Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree53Norm x).property (boundaryImPowerRow77_16Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree53Norm,boundaryImPowerRow77_16Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x))))=(boundaryImPowerRow77_14Degree53Norm x).val+(boundaryFullPowerDegree53Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree53Norm x).property (boundaryFullPowerDegree53Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree53Norm,boundaryFullPowerDegree53Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x))))))=(boundaryFullPowerDegree53Block33Norm x).val+(boundaryFullPowerDegree53Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block33Norm x).property (boundaryFullPowerDegree53Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block33Norm,boundaryFullPowerDegree53Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x))=c} := by

  have he : ((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x))=(boundaryImPowerRow77_18Degree53Norm x).val+(boundaryImPowerRow77_19Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree53Norm x).property (boundaryImPowerRow77_19Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree53Norm,boundaryImPowerRow77_19Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x))))=(boundaryImPowerRow77_17Degree53Norm x).val+(boundaryFullPowerDegree53Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree53Norm x).property (boundaryFullPowerDegree53Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree53Norm,boundaryFullPowerDegree53Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))=c} := by

  have he : ((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))=(boundaryImPowerRow77_21Degree53Norm x).val+(boundaryLowPowerRow77Degree53Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree53Norm x).property (boundaryLowPowerRow77Degree53Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree53Norm,boundaryLowPowerRow77Degree53Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))=(boundaryImPowerRow77_20Degree53Norm x).val+(boundaryFullPowerDegree53Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree53Norm x).property (boundaryFullPowerDegree53Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree53Norm,boundaryFullPowerDegree53Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))=(boundaryFullPowerDegree53Block38Norm x).val+(boundaryFullPowerDegree53Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block38Norm x).property (boundaryFullPowerDegree53Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block38Norm,boundaryFullPowerDegree53Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))))=(boundaryFullPowerDegree53Block36Norm x).val+(boundaryFullPowerDegree53Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block36Norm x).property (boundaryFullPowerDegree53Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block36Norm,boundaryFullPowerDegree53Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x)))))))))+(((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x)))))))))+(((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))))))=(boundaryFullPowerDegree53Block31Norm x).val+(boundaryFullPowerDegree53Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block31Norm x).property (boundaryFullPowerDegree53Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block31Norm,boundaryFullPowerDegree53Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree53Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x)))))))))+(((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x)))))))))))+(((((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x)))))))))+(((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x)))))))))+(((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x)))))))))))+(((((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x)))))))))+(((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x))))))))))))=(boundaryFullPowerDegree53Block21Norm x).val+(boundaryFullPowerDegree53Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree53Block21Norm x).property (boundaryFullPowerDegree53Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block21Norm,boundaryFullPowerDegree53Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree53Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 53 x=c} := by

  have he0 : boundaryFullPowerRow77 53 x=((((((((((boundaryRePowerRow77_0 53 x)+(boundaryRePowerRow77_1 53 x)))+(((boundaryRePowerRow77_2 53 x)+(((boundaryRePowerRow77_3 53 x)+(boundaryRePowerRow77_4 53 x)))))))+(((((boundaryRePowerRow77_5 53 x)+(((boundaryRePowerRow77_6 53 x)+(boundaryRePowerRow77_7 53 x)))))+(((boundaryRePowerRow77_8 53 x)+(((boundaryRePowerRow77_9 53 x)+(boundaryRePowerRow77_10 53 x)))))))))+(((((((boundaryRePowerRow77_11 53 x)+(((boundaryRePowerRow77_12 53 x)+(boundaryRePowerRow77_13 53 x)))))+(((boundaryRePowerRow77_14 53 x)+(((boundaryRePowerRow77_15 53 x)+(boundaryRePowerRow77_16 53 x)))))))+(((((boundaryRePowerRow77_17 53 x)+(((boundaryRePowerRow77_18 53 x)+(boundaryRePowerRow77_19 53 x)))))+(((boundaryRePowerRow77_20 53 x)+(((boundaryRePowerRow77_21 53 x)+(boundaryRePowerRow77_22 53 x)))))))))))+(((((((((boundaryImPowerRow77_0 53 x)+(boundaryImPowerRow77_1 53 x)))+(((boundaryImPowerRow77_2 53 x)+(((boundaryImPowerRow77_3 53 x)+(boundaryImPowerRow77_4 53 x)))))))+(((((boundaryImPowerRow77_5 53 x)+(((boundaryImPowerRow77_6 53 x)+(boundaryImPowerRow77_7 53 x)))))+(((boundaryImPowerRow77_8 53 x)+(((boundaryImPowerRow77_9 53 x)+(boundaryImPowerRow77_10 53 x)))))))))+(((((((boundaryImPowerRow77_11 53 x)+(((boundaryImPowerRow77_12 53 x)+(boundaryImPowerRow77_13 53 x)))))+(((boundaryImPowerRow77_14 53 x)+(((boundaryImPowerRow77_15 53 x)+(boundaryImPowerRow77_16 53 x)))))))+(((((boundaryImPowerRow77_17 53 x)+(((boundaryImPowerRow77_18 53 x)+(boundaryImPowerRow77_19 53 x)))))+(((boundaryImPowerRow77_20 53 x)+(((boundaryImPowerRow77_21 53 x)+(boundaryLowPowerRow77 53 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree53Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree53Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
