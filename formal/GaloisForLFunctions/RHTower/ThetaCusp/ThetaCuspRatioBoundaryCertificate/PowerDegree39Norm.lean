import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree39Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree39Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x))=c} := by

  have he : ((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x))=(boundaryRePowerRow77_0Degree39Norm x).val+(boundaryRePowerRow77_1Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree39Norm x).property (boundaryRePowerRow77_1Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree39Norm,boundaryRePowerRow77_1Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x))=c} := by

  have he : ((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x))=(boundaryRePowerRow77_3Degree39Norm x).val+(boundaryRePowerRow77_4Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree39Norm x).property (boundaryRePowerRow77_4Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree39Norm,boundaryRePowerRow77_4Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x))))=(boundaryRePowerRow77_2Degree39Norm x).val+(boundaryFullPowerDegree39Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree39Norm x).property (boundaryFullPowerDegree39Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree39Norm,boundaryFullPowerDegree39Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x))))))=(boundaryFullPowerDegree39Block0Norm x).val+(boundaryFullPowerDegree39Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block0Norm x).property (boundaryFullPowerDegree39Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block0Norm,boundaryFullPowerDegree39Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x))=c} := by

  have he : ((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x))=(boundaryRePowerRow77_6Degree39Norm x).val+(boundaryRePowerRow77_7Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree39Norm x).property (boundaryRePowerRow77_7Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree39Norm,boundaryRePowerRow77_7Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x))))=(boundaryRePowerRow77_5Degree39Norm x).val+(boundaryFullPowerDegree39Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree39Norm x).property (boundaryFullPowerDegree39Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree39Norm,boundaryFullPowerDegree39Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))=c} := by

  have he : ((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))=(boundaryRePowerRow77_9Degree39Norm x).val+(boundaryRePowerRow77_10Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree39Norm x).property (boundaryRePowerRow77_10Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree39Norm,boundaryRePowerRow77_10Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))))=(boundaryRePowerRow77_8Degree39Norm x).val+(boundaryFullPowerDegree39Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree39Norm x).property (boundaryFullPowerDegree39Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree39Norm,boundaryFullPowerDegree39Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))))))=(boundaryFullPowerDegree39Block5Norm x).val+(boundaryFullPowerDegree39Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block5Norm x).property (boundaryFullPowerDegree39Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block5Norm,boundaryFullPowerDegree39Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x))))))))=(boundaryFullPowerDegree39Block3Norm x).val+(boundaryFullPowerDegree39Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block3Norm x).property (boundaryFullPowerDegree39Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block3Norm,boundaryFullPowerDegree39Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x))=c} := by

  have he : ((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x))=(boundaryRePowerRow77_12Degree39Norm x).val+(boundaryRePowerRow77_13Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree39Norm x).property (boundaryRePowerRow77_13Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree39Norm,boundaryRePowerRow77_13Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x))))=(boundaryRePowerRow77_11Degree39Norm x).val+(boundaryFullPowerDegree39Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree39Norm x).property (boundaryFullPowerDegree39Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree39Norm,boundaryFullPowerDegree39Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x))=c} := by

  have he : ((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x))=(boundaryRePowerRow77_15Degree39Norm x).val+(boundaryRePowerRow77_16Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree39Norm x).property (boundaryRePowerRow77_16Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree39Norm,boundaryRePowerRow77_16Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x))))=(boundaryRePowerRow77_14Degree39Norm x).val+(boundaryFullPowerDegree39Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree39Norm x).property (boundaryFullPowerDegree39Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree39Norm,boundaryFullPowerDegree39Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x))))))=(boundaryFullPowerDegree39Block11Norm x).val+(boundaryFullPowerDegree39Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block11Norm x).property (boundaryFullPowerDegree39Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block11Norm,boundaryFullPowerDegree39Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x))=c} := by

  have he : ((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x))=(boundaryRePowerRow77_18Degree39Norm x).val+(boundaryRePowerRow77_19Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree39Norm x).property (boundaryRePowerRow77_19Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree39Norm,boundaryRePowerRow77_19Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x))))=(boundaryRePowerRow77_17Degree39Norm x).val+(boundaryFullPowerDegree39Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree39Norm x).property (boundaryFullPowerDegree39Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree39Norm,boundaryFullPowerDegree39Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))=c} := by

  have he : ((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))=(boundaryRePowerRow77_21Degree39Norm x).val+(boundaryRePowerRow77_22Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree39Norm x).property (boundaryRePowerRow77_22Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree39Norm,boundaryRePowerRow77_22Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))=(boundaryRePowerRow77_20Degree39Norm x).val+(boundaryFullPowerDegree39Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree39Norm x).property (boundaryFullPowerDegree39Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree39Norm,boundaryFullPowerDegree39Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))))=(boundaryFullPowerDegree39Block16Norm x).val+(boundaryFullPowerDegree39Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block16Norm x).property (boundaryFullPowerDegree39Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block16Norm,boundaryFullPowerDegree39Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))))))=(boundaryFullPowerDegree39Block14Norm x).val+(boundaryFullPowerDegree39Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block14Norm x).property (boundaryFullPowerDegree39Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block14Norm,boundaryFullPowerDegree39Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x)))))))))+(((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x)))))))))+(((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x))))))))))=(boundaryFullPowerDegree39Block9Norm x).val+(boundaryFullPowerDegree39Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block9Norm x).property (boundaryFullPowerDegree39Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block9Norm,boundaryFullPowerDegree39Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x))=c} := by

  have he : ((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x))=(boundaryImPowerRow77_0Degree39Norm x).val+(boundaryImPowerRow77_1Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree39Norm x).property (boundaryImPowerRow77_1Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree39Norm,boundaryImPowerRow77_1Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x))=c} := by

  have he : ((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x))=(boundaryImPowerRow77_3Degree39Norm x).val+(boundaryImPowerRow77_4Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree39Norm x).property (boundaryImPowerRow77_4Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree39Norm,boundaryImPowerRow77_4Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x))))=(boundaryImPowerRow77_2Degree39Norm x).val+(boundaryFullPowerDegree39Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree39Norm x).property (boundaryFullPowerDegree39Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree39Norm,boundaryFullPowerDegree39Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x))))))=(boundaryFullPowerDegree39Block22Norm x).val+(boundaryFullPowerDegree39Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block22Norm x).property (boundaryFullPowerDegree39Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block22Norm,boundaryFullPowerDegree39Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x))=c} := by

  have he : ((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x))=(boundaryImPowerRow77_6Degree39Norm x).val+(boundaryImPowerRow77_7Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree39Norm x).property (boundaryImPowerRow77_7Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree39Norm,boundaryImPowerRow77_7Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x))))=(boundaryImPowerRow77_5Degree39Norm x).val+(boundaryFullPowerDegree39Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree39Norm x).property (boundaryFullPowerDegree39Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree39Norm,boundaryFullPowerDegree39Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))=c} := by

  have he : ((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))=(boundaryImPowerRow77_9Degree39Norm x).val+(boundaryImPowerRow77_10Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree39Norm x).property (boundaryImPowerRow77_10Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree39Norm,boundaryImPowerRow77_10Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))))=(boundaryImPowerRow77_8Degree39Norm x).val+(boundaryFullPowerDegree39Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree39Norm x).property (boundaryFullPowerDegree39Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree39Norm,boundaryFullPowerDegree39Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))))))=(boundaryFullPowerDegree39Block27Norm x).val+(boundaryFullPowerDegree39Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block27Norm x).property (boundaryFullPowerDegree39Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block27Norm,boundaryFullPowerDegree39Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x))))))))=(boundaryFullPowerDegree39Block25Norm x).val+(boundaryFullPowerDegree39Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block25Norm x).property (boundaryFullPowerDegree39Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block25Norm,boundaryFullPowerDegree39Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x))=c} := by

  have he : ((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x))=(boundaryImPowerRow77_12Degree39Norm x).val+(boundaryImPowerRow77_13Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree39Norm x).property (boundaryImPowerRow77_13Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree39Norm,boundaryImPowerRow77_13Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x))))=(boundaryImPowerRow77_11Degree39Norm x).val+(boundaryFullPowerDegree39Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree39Norm x).property (boundaryFullPowerDegree39Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree39Norm,boundaryFullPowerDegree39Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x))=c} := by

  have he : ((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x))=(boundaryImPowerRow77_15Degree39Norm x).val+(boundaryImPowerRow77_16Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree39Norm x).property (boundaryImPowerRow77_16Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree39Norm,boundaryImPowerRow77_16Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x))))=(boundaryImPowerRow77_14Degree39Norm x).val+(boundaryFullPowerDegree39Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree39Norm x).property (boundaryFullPowerDegree39Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree39Norm,boundaryFullPowerDegree39Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x))))))=(boundaryFullPowerDegree39Block33Norm x).val+(boundaryFullPowerDegree39Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block33Norm x).property (boundaryFullPowerDegree39Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block33Norm,boundaryFullPowerDegree39Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x))=c} := by

  have he : ((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x))=(boundaryImPowerRow77_18Degree39Norm x).val+(boundaryImPowerRow77_19Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree39Norm x).property (boundaryImPowerRow77_19Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree39Norm,boundaryImPowerRow77_19Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x))))=(boundaryImPowerRow77_17Degree39Norm x).val+(boundaryFullPowerDegree39Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree39Norm x).property (boundaryFullPowerDegree39Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree39Norm,boundaryFullPowerDegree39Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))=c} := by

  have he : ((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))=(boundaryImPowerRow77_21Degree39Norm x).val+(boundaryLowPowerRow77Degree39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree39Norm x).property (boundaryLowPowerRow77Degree39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree39Norm,boundaryLowPowerRow77Degree39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))=(boundaryImPowerRow77_20Degree39Norm x).val+(boundaryFullPowerDegree39Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree39Norm x).property (boundaryFullPowerDegree39Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree39Norm,boundaryFullPowerDegree39Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))=(boundaryFullPowerDegree39Block38Norm x).val+(boundaryFullPowerDegree39Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block38Norm x).property (boundaryFullPowerDegree39Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block38Norm,boundaryFullPowerDegree39Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))))=(boundaryFullPowerDegree39Block36Norm x).val+(boundaryFullPowerDegree39Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block36Norm x).property (boundaryFullPowerDegree39Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block36Norm,boundaryFullPowerDegree39Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x)))))))))+(((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x)))))))))+(((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))))))=(boundaryFullPowerDegree39Block31Norm x).val+(boundaryFullPowerDegree39Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block31Norm x).property (boundaryFullPowerDegree39Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block31Norm,boundaryFullPowerDegree39Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree39Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x)))))))))+(((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x)))))))))))+(((((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x)))))))))+(((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x)))))))))+(((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x)))))))))))+(((((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x)))))))))+(((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x))))))))))))=(boundaryFullPowerDegree39Block21Norm x).val+(boundaryFullPowerDegree39Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree39Block21Norm x).property (boundaryFullPowerDegree39Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block21Norm,boundaryFullPowerDegree39Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree39Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 39 x=c} := by

  have he0 : boundaryFullPowerRow77 39 x=((((((((((boundaryRePowerRow77_0 39 x)+(boundaryRePowerRow77_1 39 x)))+(((boundaryRePowerRow77_2 39 x)+(((boundaryRePowerRow77_3 39 x)+(boundaryRePowerRow77_4 39 x)))))))+(((((boundaryRePowerRow77_5 39 x)+(((boundaryRePowerRow77_6 39 x)+(boundaryRePowerRow77_7 39 x)))))+(((boundaryRePowerRow77_8 39 x)+(((boundaryRePowerRow77_9 39 x)+(boundaryRePowerRow77_10 39 x)))))))))+(((((((boundaryRePowerRow77_11 39 x)+(((boundaryRePowerRow77_12 39 x)+(boundaryRePowerRow77_13 39 x)))))+(((boundaryRePowerRow77_14 39 x)+(((boundaryRePowerRow77_15 39 x)+(boundaryRePowerRow77_16 39 x)))))))+(((((boundaryRePowerRow77_17 39 x)+(((boundaryRePowerRow77_18 39 x)+(boundaryRePowerRow77_19 39 x)))))+(((boundaryRePowerRow77_20 39 x)+(((boundaryRePowerRow77_21 39 x)+(boundaryRePowerRow77_22 39 x)))))))))))+(((((((((boundaryImPowerRow77_0 39 x)+(boundaryImPowerRow77_1 39 x)))+(((boundaryImPowerRow77_2 39 x)+(((boundaryImPowerRow77_3 39 x)+(boundaryImPowerRow77_4 39 x)))))))+(((((boundaryImPowerRow77_5 39 x)+(((boundaryImPowerRow77_6 39 x)+(boundaryImPowerRow77_7 39 x)))))+(((boundaryImPowerRow77_8 39 x)+(((boundaryImPowerRow77_9 39 x)+(boundaryImPowerRow77_10 39 x)))))))))+(((((((boundaryImPowerRow77_11 39 x)+(((boundaryImPowerRow77_12 39 x)+(boundaryImPowerRow77_13 39 x)))))+(((boundaryImPowerRow77_14 39 x)+(((boundaryImPowerRow77_15 39 x)+(boundaryImPowerRow77_16 39 x)))))))+(((((boundaryImPowerRow77_17 39 x)+(((boundaryImPowerRow77_18 39 x)+(boundaryImPowerRow77_19 39 x)))))+(((boundaryImPowerRow77_20 39 x)+(((boundaryImPowerRow77_21 39 x)+(boundaryLowPowerRow77 39 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree39Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree39Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
