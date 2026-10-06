import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree95Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree95Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x))=c} := by

  have he : ((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x))=(boundaryRePowerRow77_0Degree95Norm x).val+(boundaryRePowerRow77_1Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree95Norm x).property (boundaryRePowerRow77_1Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree95Norm,boundaryRePowerRow77_1Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x))=c} := by

  have he : ((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x))=(boundaryRePowerRow77_3Degree95Norm x).val+(boundaryRePowerRow77_4Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree95Norm x).property (boundaryRePowerRow77_4Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree95Norm,boundaryRePowerRow77_4Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x))))=(boundaryRePowerRow77_2Degree95Norm x).val+(boundaryFullPowerDegree95Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree95Norm x).property (boundaryFullPowerDegree95Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree95Norm,boundaryFullPowerDegree95Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x))))))=(boundaryFullPowerDegree95Block0Norm x).val+(boundaryFullPowerDegree95Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block0Norm x).property (boundaryFullPowerDegree95Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block0Norm,boundaryFullPowerDegree95Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x))=c} := by

  have he : ((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x))=(boundaryRePowerRow77_6Degree95Norm x).val+(boundaryRePowerRow77_7Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree95Norm x).property (boundaryRePowerRow77_7Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree95Norm,boundaryRePowerRow77_7Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x))))=(boundaryRePowerRow77_5Degree95Norm x).val+(boundaryFullPowerDegree95Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree95Norm x).property (boundaryFullPowerDegree95Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree95Norm,boundaryFullPowerDegree95Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))=c} := by

  have he : ((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))=(boundaryRePowerRow77_9Degree95Norm x).val+(boundaryRePowerRow77_10Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree95Norm x).property (boundaryRePowerRow77_10Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree95Norm,boundaryRePowerRow77_10Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))))=(boundaryRePowerRow77_8Degree95Norm x).val+(boundaryFullPowerDegree95Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree95Norm x).property (boundaryFullPowerDegree95Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree95Norm,boundaryFullPowerDegree95Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))))))=(boundaryFullPowerDegree95Block5Norm x).val+(boundaryFullPowerDegree95Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block5Norm x).property (boundaryFullPowerDegree95Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block5Norm,boundaryFullPowerDegree95Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x))))))))=(boundaryFullPowerDegree95Block3Norm x).val+(boundaryFullPowerDegree95Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block3Norm x).property (boundaryFullPowerDegree95Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block3Norm,boundaryFullPowerDegree95Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x))=c} := by

  have he : ((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x))=(boundaryRePowerRow77_12Degree95Norm x).val+(boundaryRePowerRow77_13Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree95Norm x).property (boundaryRePowerRow77_13Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree95Norm,boundaryRePowerRow77_13Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x))))=(boundaryRePowerRow77_11Degree95Norm x).val+(boundaryFullPowerDegree95Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree95Norm x).property (boundaryFullPowerDegree95Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree95Norm,boundaryFullPowerDegree95Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x))=c} := by

  have he : ((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x))=(boundaryRePowerRow77_15Degree95Norm x).val+(boundaryRePowerRow77_16Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree95Norm x).property (boundaryRePowerRow77_16Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree95Norm,boundaryRePowerRow77_16Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x))))=(boundaryRePowerRow77_14Degree95Norm x).val+(boundaryFullPowerDegree95Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree95Norm x).property (boundaryFullPowerDegree95Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree95Norm,boundaryFullPowerDegree95Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x))))))=(boundaryFullPowerDegree95Block11Norm x).val+(boundaryFullPowerDegree95Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block11Norm x).property (boundaryFullPowerDegree95Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block11Norm,boundaryFullPowerDegree95Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x))=c} := by

  have he : ((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x))=(boundaryRePowerRow77_18Degree95Norm x).val+(boundaryRePowerRow77_19Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree95Norm x).property (boundaryRePowerRow77_19Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree95Norm,boundaryRePowerRow77_19Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x))))=(boundaryRePowerRow77_17Degree95Norm x).val+(boundaryFullPowerDegree95Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree95Norm x).property (boundaryFullPowerDegree95Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree95Norm,boundaryFullPowerDegree95Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))=c} := by

  have he : ((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))=(boundaryRePowerRow77_21Degree95Norm x).val+(boundaryRePowerRow77_22Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree95Norm x).property (boundaryRePowerRow77_22Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree95Norm,boundaryRePowerRow77_22Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))=(boundaryRePowerRow77_20Degree95Norm x).val+(boundaryFullPowerDegree95Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree95Norm x).property (boundaryFullPowerDegree95Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree95Norm,boundaryFullPowerDegree95Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))))=(boundaryFullPowerDegree95Block16Norm x).val+(boundaryFullPowerDegree95Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block16Norm x).property (boundaryFullPowerDegree95Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block16Norm,boundaryFullPowerDegree95Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))))))=(boundaryFullPowerDegree95Block14Norm x).val+(boundaryFullPowerDegree95Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block14Norm x).property (boundaryFullPowerDegree95Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block14Norm,boundaryFullPowerDegree95Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x)))))))))+(((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x)))))))))+(((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x))))))))))=(boundaryFullPowerDegree95Block9Norm x).val+(boundaryFullPowerDegree95Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block9Norm x).property (boundaryFullPowerDegree95Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block9Norm,boundaryFullPowerDegree95Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x))=c} := by

  have he : ((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x))=(boundaryImPowerRow77_0Degree95Norm x).val+(boundaryImPowerRow77_1Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree95Norm x).property (boundaryImPowerRow77_1Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree95Norm,boundaryImPowerRow77_1Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x))=c} := by

  have he : ((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x))=(boundaryImPowerRow77_3Degree95Norm x).val+(boundaryImPowerRow77_4Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree95Norm x).property (boundaryImPowerRow77_4Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree95Norm,boundaryImPowerRow77_4Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x))))=(boundaryImPowerRow77_2Degree95Norm x).val+(boundaryFullPowerDegree95Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree95Norm x).property (boundaryFullPowerDegree95Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree95Norm,boundaryFullPowerDegree95Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x))))))=(boundaryFullPowerDegree95Block22Norm x).val+(boundaryFullPowerDegree95Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block22Norm x).property (boundaryFullPowerDegree95Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block22Norm,boundaryFullPowerDegree95Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x))=c} := by

  have he : ((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x))=(boundaryImPowerRow77_6Degree95Norm x).val+(boundaryImPowerRow77_7Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree95Norm x).property (boundaryImPowerRow77_7Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree95Norm,boundaryImPowerRow77_7Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x))))=(boundaryImPowerRow77_5Degree95Norm x).val+(boundaryFullPowerDegree95Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree95Norm x).property (boundaryFullPowerDegree95Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree95Norm,boundaryFullPowerDegree95Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))=c} := by

  have he : ((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))=(boundaryImPowerRow77_9Degree95Norm x).val+(boundaryImPowerRow77_10Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree95Norm x).property (boundaryImPowerRow77_10Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree95Norm,boundaryImPowerRow77_10Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))))=(boundaryImPowerRow77_8Degree95Norm x).val+(boundaryFullPowerDegree95Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree95Norm x).property (boundaryFullPowerDegree95Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree95Norm,boundaryFullPowerDegree95Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))))))=(boundaryFullPowerDegree95Block27Norm x).val+(boundaryFullPowerDegree95Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block27Norm x).property (boundaryFullPowerDegree95Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block27Norm,boundaryFullPowerDegree95Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x))))))))=(boundaryFullPowerDegree95Block25Norm x).val+(boundaryFullPowerDegree95Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block25Norm x).property (boundaryFullPowerDegree95Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block25Norm,boundaryFullPowerDegree95Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x))=c} := by

  have he : ((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x))=(boundaryImPowerRow77_12Degree95Norm x).val+(boundaryImPowerRow77_13Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree95Norm x).property (boundaryImPowerRow77_13Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree95Norm,boundaryImPowerRow77_13Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x))))=(boundaryImPowerRow77_11Degree95Norm x).val+(boundaryFullPowerDegree95Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree95Norm x).property (boundaryFullPowerDegree95Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree95Norm,boundaryFullPowerDegree95Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x))=c} := by

  have he : ((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x))=(boundaryImPowerRow77_15Degree95Norm x).val+(boundaryImPowerRow77_16Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree95Norm x).property (boundaryImPowerRow77_16Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree95Norm,boundaryImPowerRow77_16Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x))))=(boundaryImPowerRow77_14Degree95Norm x).val+(boundaryFullPowerDegree95Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree95Norm x).property (boundaryFullPowerDegree95Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree95Norm,boundaryFullPowerDegree95Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x))))))=(boundaryFullPowerDegree95Block33Norm x).val+(boundaryFullPowerDegree95Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block33Norm x).property (boundaryFullPowerDegree95Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block33Norm,boundaryFullPowerDegree95Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x))=c} := by

  have he : ((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x))=(boundaryImPowerRow77_18Degree95Norm x).val+(boundaryImPowerRow77_19Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree95Norm x).property (boundaryImPowerRow77_19Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree95Norm,boundaryImPowerRow77_19Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x))))=(boundaryImPowerRow77_17Degree95Norm x).val+(boundaryFullPowerDegree95Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree95Norm x).property (boundaryFullPowerDegree95Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree95Norm,boundaryFullPowerDegree95Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))=c} := by

  have he : ((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))=(boundaryImPowerRow77_21Degree95Norm x).val+(boundaryLowPowerRow77Degree95Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree95Norm x).property (boundaryLowPowerRow77Degree95Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree95Norm,boundaryLowPowerRow77Degree95Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))=(boundaryImPowerRow77_20Degree95Norm x).val+(boundaryFullPowerDegree95Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree95Norm x).property (boundaryFullPowerDegree95Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree95Norm,boundaryFullPowerDegree95Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))=(boundaryFullPowerDegree95Block38Norm x).val+(boundaryFullPowerDegree95Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block38Norm x).property (boundaryFullPowerDegree95Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block38Norm,boundaryFullPowerDegree95Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))))=(boundaryFullPowerDegree95Block36Norm x).val+(boundaryFullPowerDegree95Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block36Norm x).property (boundaryFullPowerDegree95Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block36Norm,boundaryFullPowerDegree95Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x)))))))))+(((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x)))))))))+(((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))))))=(boundaryFullPowerDegree95Block31Norm x).val+(boundaryFullPowerDegree95Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block31Norm x).property (boundaryFullPowerDegree95Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block31Norm,boundaryFullPowerDegree95Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree95Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x)))))))))+(((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x)))))))))))+(((((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x)))))))))+(((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x)))))))))+(((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x)))))))))))+(((((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x)))))))))+(((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x))))))))))))=(boundaryFullPowerDegree95Block21Norm x).val+(boundaryFullPowerDegree95Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree95Block21Norm x).property (boundaryFullPowerDegree95Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block21Norm,boundaryFullPowerDegree95Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree95Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 95 x=c} := by

  have he0 : boundaryFullPowerRow77 95 x=((((((((((boundaryRePowerRow77_0 95 x)+(boundaryRePowerRow77_1 95 x)))+(((boundaryRePowerRow77_2 95 x)+(((boundaryRePowerRow77_3 95 x)+(boundaryRePowerRow77_4 95 x)))))))+(((((boundaryRePowerRow77_5 95 x)+(((boundaryRePowerRow77_6 95 x)+(boundaryRePowerRow77_7 95 x)))))+(((boundaryRePowerRow77_8 95 x)+(((boundaryRePowerRow77_9 95 x)+(boundaryRePowerRow77_10 95 x)))))))))+(((((((boundaryRePowerRow77_11 95 x)+(((boundaryRePowerRow77_12 95 x)+(boundaryRePowerRow77_13 95 x)))))+(((boundaryRePowerRow77_14 95 x)+(((boundaryRePowerRow77_15 95 x)+(boundaryRePowerRow77_16 95 x)))))))+(((((boundaryRePowerRow77_17 95 x)+(((boundaryRePowerRow77_18 95 x)+(boundaryRePowerRow77_19 95 x)))))+(((boundaryRePowerRow77_20 95 x)+(((boundaryRePowerRow77_21 95 x)+(boundaryRePowerRow77_22 95 x)))))))))))+(((((((((boundaryImPowerRow77_0 95 x)+(boundaryImPowerRow77_1 95 x)))+(((boundaryImPowerRow77_2 95 x)+(((boundaryImPowerRow77_3 95 x)+(boundaryImPowerRow77_4 95 x)))))))+(((((boundaryImPowerRow77_5 95 x)+(((boundaryImPowerRow77_6 95 x)+(boundaryImPowerRow77_7 95 x)))))+(((boundaryImPowerRow77_8 95 x)+(((boundaryImPowerRow77_9 95 x)+(boundaryImPowerRow77_10 95 x)))))))))+(((((((boundaryImPowerRow77_11 95 x)+(((boundaryImPowerRow77_12 95 x)+(boundaryImPowerRow77_13 95 x)))))+(((boundaryImPowerRow77_14 95 x)+(((boundaryImPowerRow77_15 95 x)+(boundaryImPowerRow77_16 95 x)))))))+(((((boundaryImPowerRow77_17 95 x)+(((boundaryImPowerRow77_18 95 x)+(boundaryImPowerRow77_19 95 x)))))+(((boundaryImPowerRow77_20 95 x)+(((boundaryImPowerRow77_21 95 x)+(boundaryLowPowerRow77 95 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree95Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree95Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
