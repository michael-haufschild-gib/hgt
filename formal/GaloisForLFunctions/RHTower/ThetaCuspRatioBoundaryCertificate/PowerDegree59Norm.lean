import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree59Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree59Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x))=c} := by

  have he : ((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x))=(boundaryRePowerRow77_0Degree59Norm x).val+(boundaryRePowerRow77_1Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree59Norm x).property (boundaryRePowerRow77_1Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree59Norm,boundaryRePowerRow77_1Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x))=c} := by

  have he : ((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x))=(boundaryRePowerRow77_3Degree59Norm x).val+(boundaryRePowerRow77_4Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree59Norm x).property (boundaryRePowerRow77_4Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree59Norm,boundaryRePowerRow77_4Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x))))=(boundaryRePowerRow77_2Degree59Norm x).val+(boundaryFullPowerDegree59Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree59Norm x).property (boundaryFullPowerDegree59Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree59Norm,boundaryFullPowerDegree59Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x))))))=(boundaryFullPowerDegree59Block0Norm x).val+(boundaryFullPowerDegree59Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block0Norm x).property (boundaryFullPowerDegree59Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block0Norm,boundaryFullPowerDegree59Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x))=c} := by

  have he : ((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x))=(boundaryRePowerRow77_6Degree59Norm x).val+(boundaryRePowerRow77_7Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree59Norm x).property (boundaryRePowerRow77_7Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree59Norm,boundaryRePowerRow77_7Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x))))=(boundaryRePowerRow77_5Degree59Norm x).val+(boundaryFullPowerDegree59Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree59Norm x).property (boundaryFullPowerDegree59Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree59Norm,boundaryFullPowerDegree59Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))=c} := by

  have he : ((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))=(boundaryRePowerRow77_9Degree59Norm x).val+(boundaryRePowerRow77_10Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree59Norm x).property (boundaryRePowerRow77_10Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree59Norm,boundaryRePowerRow77_10Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))))=(boundaryRePowerRow77_8Degree59Norm x).val+(boundaryFullPowerDegree59Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree59Norm x).property (boundaryFullPowerDegree59Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree59Norm,boundaryFullPowerDegree59Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))))))=(boundaryFullPowerDegree59Block5Norm x).val+(boundaryFullPowerDegree59Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block5Norm x).property (boundaryFullPowerDegree59Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block5Norm,boundaryFullPowerDegree59Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x))))))))=(boundaryFullPowerDegree59Block3Norm x).val+(boundaryFullPowerDegree59Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block3Norm x).property (boundaryFullPowerDegree59Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block3Norm,boundaryFullPowerDegree59Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x))=c} := by

  have he : ((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x))=(boundaryRePowerRow77_12Degree59Norm x).val+(boundaryRePowerRow77_13Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree59Norm x).property (boundaryRePowerRow77_13Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree59Norm,boundaryRePowerRow77_13Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x))))=(boundaryRePowerRow77_11Degree59Norm x).val+(boundaryFullPowerDegree59Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree59Norm x).property (boundaryFullPowerDegree59Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree59Norm,boundaryFullPowerDegree59Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x))=c} := by

  have he : ((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x))=(boundaryRePowerRow77_15Degree59Norm x).val+(boundaryRePowerRow77_16Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree59Norm x).property (boundaryRePowerRow77_16Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree59Norm,boundaryRePowerRow77_16Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x))))=(boundaryRePowerRow77_14Degree59Norm x).val+(boundaryFullPowerDegree59Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree59Norm x).property (boundaryFullPowerDegree59Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree59Norm,boundaryFullPowerDegree59Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x))))))=(boundaryFullPowerDegree59Block11Norm x).val+(boundaryFullPowerDegree59Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block11Norm x).property (boundaryFullPowerDegree59Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block11Norm,boundaryFullPowerDegree59Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x))=c} := by

  have he : ((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x))=(boundaryRePowerRow77_18Degree59Norm x).val+(boundaryRePowerRow77_19Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree59Norm x).property (boundaryRePowerRow77_19Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree59Norm,boundaryRePowerRow77_19Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x))))=(boundaryRePowerRow77_17Degree59Norm x).val+(boundaryFullPowerDegree59Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree59Norm x).property (boundaryFullPowerDegree59Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree59Norm,boundaryFullPowerDegree59Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))=c} := by

  have he : ((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))=(boundaryRePowerRow77_21Degree59Norm x).val+(boundaryRePowerRow77_22Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree59Norm x).property (boundaryRePowerRow77_22Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree59Norm,boundaryRePowerRow77_22Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))=(boundaryRePowerRow77_20Degree59Norm x).val+(boundaryFullPowerDegree59Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree59Norm x).property (boundaryFullPowerDegree59Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree59Norm,boundaryFullPowerDegree59Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))))=(boundaryFullPowerDegree59Block16Norm x).val+(boundaryFullPowerDegree59Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block16Norm x).property (boundaryFullPowerDegree59Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block16Norm,boundaryFullPowerDegree59Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))))))=(boundaryFullPowerDegree59Block14Norm x).val+(boundaryFullPowerDegree59Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block14Norm x).property (boundaryFullPowerDegree59Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block14Norm,boundaryFullPowerDegree59Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x)))))))))+(((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x)))))))))+(((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x))))))))))=(boundaryFullPowerDegree59Block9Norm x).val+(boundaryFullPowerDegree59Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block9Norm x).property (boundaryFullPowerDegree59Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block9Norm,boundaryFullPowerDegree59Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x))=c} := by

  have he : ((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x))=(boundaryImPowerRow77_0Degree59Norm x).val+(boundaryImPowerRow77_1Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree59Norm x).property (boundaryImPowerRow77_1Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree59Norm,boundaryImPowerRow77_1Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x))=c} := by

  have he : ((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x))=(boundaryImPowerRow77_3Degree59Norm x).val+(boundaryImPowerRow77_4Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree59Norm x).property (boundaryImPowerRow77_4Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree59Norm,boundaryImPowerRow77_4Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x))))=(boundaryImPowerRow77_2Degree59Norm x).val+(boundaryFullPowerDegree59Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree59Norm x).property (boundaryFullPowerDegree59Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree59Norm,boundaryFullPowerDegree59Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x))))))=(boundaryFullPowerDegree59Block22Norm x).val+(boundaryFullPowerDegree59Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block22Norm x).property (boundaryFullPowerDegree59Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block22Norm,boundaryFullPowerDegree59Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x))=c} := by

  have he : ((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x))=(boundaryImPowerRow77_6Degree59Norm x).val+(boundaryImPowerRow77_7Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree59Norm x).property (boundaryImPowerRow77_7Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree59Norm,boundaryImPowerRow77_7Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x))))=(boundaryImPowerRow77_5Degree59Norm x).val+(boundaryFullPowerDegree59Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree59Norm x).property (boundaryFullPowerDegree59Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree59Norm,boundaryFullPowerDegree59Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))=c} := by

  have he : ((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))=(boundaryImPowerRow77_9Degree59Norm x).val+(boundaryImPowerRow77_10Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree59Norm x).property (boundaryImPowerRow77_10Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree59Norm,boundaryImPowerRow77_10Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))))=(boundaryImPowerRow77_8Degree59Norm x).val+(boundaryFullPowerDegree59Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree59Norm x).property (boundaryFullPowerDegree59Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree59Norm,boundaryFullPowerDegree59Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))))))=(boundaryFullPowerDegree59Block27Norm x).val+(boundaryFullPowerDegree59Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block27Norm x).property (boundaryFullPowerDegree59Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block27Norm,boundaryFullPowerDegree59Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x))))))))=(boundaryFullPowerDegree59Block25Norm x).val+(boundaryFullPowerDegree59Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block25Norm x).property (boundaryFullPowerDegree59Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block25Norm,boundaryFullPowerDegree59Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x))=c} := by

  have he : ((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x))=(boundaryImPowerRow77_12Degree59Norm x).val+(boundaryImPowerRow77_13Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree59Norm x).property (boundaryImPowerRow77_13Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree59Norm,boundaryImPowerRow77_13Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x))))=(boundaryImPowerRow77_11Degree59Norm x).val+(boundaryFullPowerDegree59Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree59Norm x).property (boundaryFullPowerDegree59Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree59Norm,boundaryFullPowerDegree59Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x))=c} := by

  have he : ((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x))=(boundaryImPowerRow77_15Degree59Norm x).val+(boundaryImPowerRow77_16Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree59Norm x).property (boundaryImPowerRow77_16Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree59Norm,boundaryImPowerRow77_16Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x))))=(boundaryImPowerRow77_14Degree59Norm x).val+(boundaryFullPowerDegree59Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree59Norm x).property (boundaryFullPowerDegree59Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree59Norm,boundaryFullPowerDegree59Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x))))))=(boundaryFullPowerDegree59Block33Norm x).val+(boundaryFullPowerDegree59Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block33Norm x).property (boundaryFullPowerDegree59Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block33Norm,boundaryFullPowerDegree59Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x))=c} := by

  have he : ((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x))=(boundaryImPowerRow77_18Degree59Norm x).val+(boundaryImPowerRow77_19Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree59Norm x).property (boundaryImPowerRow77_19Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree59Norm,boundaryImPowerRow77_19Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x))))=(boundaryImPowerRow77_17Degree59Norm x).val+(boundaryFullPowerDegree59Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree59Norm x).property (boundaryFullPowerDegree59Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree59Norm,boundaryFullPowerDegree59Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))=c} := by

  have he : ((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))=(boundaryImPowerRow77_21Degree59Norm x).val+(boundaryLowPowerRow77Degree59Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree59Norm x).property (boundaryLowPowerRow77Degree59Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree59Norm,boundaryLowPowerRow77Degree59Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))=(boundaryImPowerRow77_20Degree59Norm x).val+(boundaryFullPowerDegree59Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree59Norm x).property (boundaryFullPowerDegree59Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree59Norm,boundaryFullPowerDegree59Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))=(boundaryFullPowerDegree59Block38Norm x).val+(boundaryFullPowerDegree59Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block38Norm x).property (boundaryFullPowerDegree59Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block38Norm,boundaryFullPowerDegree59Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))))=(boundaryFullPowerDegree59Block36Norm x).val+(boundaryFullPowerDegree59Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block36Norm x).property (boundaryFullPowerDegree59Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block36Norm,boundaryFullPowerDegree59Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x)))))))))+(((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x)))))))))+(((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))))))=(boundaryFullPowerDegree59Block31Norm x).val+(boundaryFullPowerDegree59Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block31Norm x).property (boundaryFullPowerDegree59Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block31Norm,boundaryFullPowerDegree59Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree59Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x)))))))))+(((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x)))))))))))+(((((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x)))))))))+(((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x)))))))))+(((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x)))))))))))+(((((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x)))))))))+(((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x))))))))))))=(boundaryFullPowerDegree59Block21Norm x).val+(boundaryFullPowerDegree59Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree59Block21Norm x).property (boundaryFullPowerDegree59Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block21Norm,boundaryFullPowerDegree59Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree59Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 59 x=c} := by

  have he0 : boundaryFullPowerRow77 59 x=((((((((((boundaryRePowerRow77_0 59 x)+(boundaryRePowerRow77_1 59 x)))+(((boundaryRePowerRow77_2 59 x)+(((boundaryRePowerRow77_3 59 x)+(boundaryRePowerRow77_4 59 x)))))))+(((((boundaryRePowerRow77_5 59 x)+(((boundaryRePowerRow77_6 59 x)+(boundaryRePowerRow77_7 59 x)))))+(((boundaryRePowerRow77_8 59 x)+(((boundaryRePowerRow77_9 59 x)+(boundaryRePowerRow77_10 59 x)))))))))+(((((((boundaryRePowerRow77_11 59 x)+(((boundaryRePowerRow77_12 59 x)+(boundaryRePowerRow77_13 59 x)))))+(((boundaryRePowerRow77_14 59 x)+(((boundaryRePowerRow77_15 59 x)+(boundaryRePowerRow77_16 59 x)))))))+(((((boundaryRePowerRow77_17 59 x)+(((boundaryRePowerRow77_18 59 x)+(boundaryRePowerRow77_19 59 x)))))+(((boundaryRePowerRow77_20 59 x)+(((boundaryRePowerRow77_21 59 x)+(boundaryRePowerRow77_22 59 x)))))))))))+(((((((((boundaryImPowerRow77_0 59 x)+(boundaryImPowerRow77_1 59 x)))+(((boundaryImPowerRow77_2 59 x)+(((boundaryImPowerRow77_3 59 x)+(boundaryImPowerRow77_4 59 x)))))))+(((((boundaryImPowerRow77_5 59 x)+(((boundaryImPowerRow77_6 59 x)+(boundaryImPowerRow77_7 59 x)))))+(((boundaryImPowerRow77_8 59 x)+(((boundaryImPowerRow77_9 59 x)+(boundaryImPowerRow77_10 59 x)))))))))+(((((((boundaryImPowerRow77_11 59 x)+(((boundaryImPowerRow77_12 59 x)+(boundaryImPowerRow77_13 59 x)))))+(((boundaryImPowerRow77_14 59 x)+(((boundaryImPowerRow77_15 59 x)+(boundaryImPowerRow77_16 59 x)))))))+(((((boundaryImPowerRow77_17 59 x)+(((boundaryImPowerRow77_18 59 x)+(boundaryImPowerRow77_19 59 x)))))+(((boundaryImPowerRow77_20 59 x)+(((boundaryImPowerRow77_21 59 x)+(boundaryLowPowerRow77 59 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree59Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree59Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
