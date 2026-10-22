import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree72Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree72Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x))=c} := by

  have he : ((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x))=(boundaryRePowerRow77_0Degree72Norm x).val+(boundaryRePowerRow77_1Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree72Norm x).property (boundaryRePowerRow77_1Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree72Norm,boundaryRePowerRow77_1Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x))=c} := by

  have he : ((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x))=(boundaryRePowerRow77_3Degree72Norm x).val+(boundaryRePowerRow77_4Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree72Norm x).property (boundaryRePowerRow77_4Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree72Norm,boundaryRePowerRow77_4Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x))))=(boundaryRePowerRow77_2Degree72Norm x).val+(boundaryFullPowerDegree72Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree72Norm x).property (boundaryFullPowerDegree72Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree72Norm,boundaryFullPowerDegree72Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x))))))=(boundaryFullPowerDegree72Block0Norm x).val+(boundaryFullPowerDegree72Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block0Norm x).property (boundaryFullPowerDegree72Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block0Norm,boundaryFullPowerDegree72Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x))=c} := by

  have he : ((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x))=(boundaryRePowerRow77_6Degree72Norm x).val+(boundaryRePowerRow77_7Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree72Norm x).property (boundaryRePowerRow77_7Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree72Norm,boundaryRePowerRow77_7Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x))))=(boundaryRePowerRow77_5Degree72Norm x).val+(boundaryFullPowerDegree72Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree72Norm x).property (boundaryFullPowerDegree72Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree72Norm,boundaryFullPowerDegree72Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))=c} := by

  have he : ((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))=(boundaryRePowerRow77_9Degree72Norm x).val+(boundaryRePowerRow77_10Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree72Norm x).property (boundaryRePowerRow77_10Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree72Norm,boundaryRePowerRow77_10Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))))=(boundaryRePowerRow77_8Degree72Norm x).val+(boundaryFullPowerDegree72Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree72Norm x).property (boundaryFullPowerDegree72Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree72Norm,boundaryFullPowerDegree72Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))))))=(boundaryFullPowerDegree72Block5Norm x).val+(boundaryFullPowerDegree72Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block5Norm x).property (boundaryFullPowerDegree72Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block5Norm,boundaryFullPowerDegree72Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x))))))))=(boundaryFullPowerDegree72Block3Norm x).val+(boundaryFullPowerDegree72Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block3Norm x).property (boundaryFullPowerDegree72Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block3Norm,boundaryFullPowerDegree72Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x))=c} := by

  have he : ((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x))=(boundaryRePowerRow77_12Degree72Norm x).val+(boundaryRePowerRow77_13Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree72Norm x).property (boundaryRePowerRow77_13Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree72Norm,boundaryRePowerRow77_13Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x))))=(boundaryRePowerRow77_11Degree72Norm x).val+(boundaryFullPowerDegree72Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree72Norm x).property (boundaryFullPowerDegree72Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree72Norm,boundaryFullPowerDegree72Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x))=c} := by

  have he : ((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x))=(boundaryRePowerRow77_15Degree72Norm x).val+(boundaryRePowerRow77_16Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree72Norm x).property (boundaryRePowerRow77_16Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree72Norm,boundaryRePowerRow77_16Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x))))=(boundaryRePowerRow77_14Degree72Norm x).val+(boundaryFullPowerDegree72Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree72Norm x).property (boundaryFullPowerDegree72Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree72Norm,boundaryFullPowerDegree72Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x))))))=(boundaryFullPowerDegree72Block11Norm x).val+(boundaryFullPowerDegree72Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block11Norm x).property (boundaryFullPowerDegree72Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block11Norm,boundaryFullPowerDegree72Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x))=c} := by

  have he : ((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x))=(boundaryRePowerRow77_18Degree72Norm x).val+(boundaryRePowerRow77_19Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree72Norm x).property (boundaryRePowerRow77_19Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree72Norm,boundaryRePowerRow77_19Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x))))=(boundaryRePowerRow77_17Degree72Norm x).val+(boundaryFullPowerDegree72Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree72Norm x).property (boundaryFullPowerDegree72Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree72Norm,boundaryFullPowerDegree72Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))=c} := by

  have he : ((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))=(boundaryRePowerRow77_21Degree72Norm x).val+(boundaryRePowerRow77_22Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree72Norm x).property (boundaryRePowerRow77_22Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree72Norm,boundaryRePowerRow77_22Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))=(boundaryRePowerRow77_20Degree72Norm x).val+(boundaryFullPowerDegree72Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree72Norm x).property (boundaryFullPowerDegree72Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree72Norm,boundaryFullPowerDegree72Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))))=(boundaryFullPowerDegree72Block16Norm x).val+(boundaryFullPowerDegree72Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block16Norm x).property (boundaryFullPowerDegree72Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block16Norm,boundaryFullPowerDegree72Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))))))=(boundaryFullPowerDegree72Block14Norm x).val+(boundaryFullPowerDegree72Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block14Norm x).property (boundaryFullPowerDegree72Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block14Norm,boundaryFullPowerDegree72Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x)))))))))+(((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x)))))))))+(((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x))))))))))=(boundaryFullPowerDegree72Block9Norm x).val+(boundaryFullPowerDegree72Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block9Norm x).property (boundaryFullPowerDegree72Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block9Norm,boundaryFullPowerDegree72Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x))=c} := by

  have he : ((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x))=(boundaryImPowerRow77_0Degree72Norm x).val+(boundaryImPowerRow77_1Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree72Norm x).property (boundaryImPowerRow77_1Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree72Norm,boundaryImPowerRow77_1Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x))=c} := by

  have he : ((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x))=(boundaryImPowerRow77_3Degree72Norm x).val+(boundaryImPowerRow77_4Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree72Norm x).property (boundaryImPowerRow77_4Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree72Norm,boundaryImPowerRow77_4Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x))))=(boundaryImPowerRow77_2Degree72Norm x).val+(boundaryFullPowerDegree72Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree72Norm x).property (boundaryFullPowerDegree72Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree72Norm,boundaryFullPowerDegree72Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x))))))=(boundaryFullPowerDegree72Block22Norm x).val+(boundaryFullPowerDegree72Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block22Norm x).property (boundaryFullPowerDegree72Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block22Norm,boundaryFullPowerDegree72Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x))=c} := by

  have he : ((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x))=(boundaryImPowerRow77_6Degree72Norm x).val+(boundaryImPowerRow77_7Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree72Norm x).property (boundaryImPowerRow77_7Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree72Norm,boundaryImPowerRow77_7Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x))))=(boundaryImPowerRow77_5Degree72Norm x).val+(boundaryFullPowerDegree72Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree72Norm x).property (boundaryFullPowerDegree72Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree72Norm,boundaryFullPowerDegree72Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))=c} := by

  have he : ((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))=(boundaryImPowerRow77_9Degree72Norm x).val+(boundaryImPowerRow77_10Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree72Norm x).property (boundaryImPowerRow77_10Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree72Norm,boundaryImPowerRow77_10Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))))=(boundaryImPowerRow77_8Degree72Norm x).val+(boundaryFullPowerDegree72Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree72Norm x).property (boundaryFullPowerDegree72Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree72Norm,boundaryFullPowerDegree72Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))))))=(boundaryFullPowerDegree72Block27Norm x).val+(boundaryFullPowerDegree72Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block27Norm x).property (boundaryFullPowerDegree72Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block27Norm,boundaryFullPowerDegree72Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x))))))))=(boundaryFullPowerDegree72Block25Norm x).val+(boundaryFullPowerDegree72Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block25Norm x).property (boundaryFullPowerDegree72Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block25Norm,boundaryFullPowerDegree72Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x))=c} := by

  have he : ((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x))=(boundaryImPowerRow77_12Degree72Norm x).val+(boundaryImPowerRow77_13Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree72Norm x).property (boundaryImPowerRow77_13Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree72Norm,boundaryImPowerRow77_13Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x))))=(boundaryImPowerRow77_11Degree72Norm x).val+(boundaryFullPowerDegree72Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree72Norm x).property (boundaryFullPowerDegree72Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree72Norm,boundaryFullPowerDegree72Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x))=c} := by

  have he : ((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x))=(boundaryImPowerRow77_15Degree72Norm x).val+(boundaryImPowerRow77_16Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree72Norm x).property (boundaryImPowerRow77_16Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree72Norm,boundaryImPowerRow77_16Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x))))=(boundaryImPowerRow77_14Degree72Norm x).val+(boundaryFullPowerDegree72Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree72Norm x).property (boundaryFullPowerDegree72Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree72Norm,boundaryFullPowerDegree72Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x))))))=(boundaryFullPowerDegree72Block33Norm x).val+(boundaryFullPowerDegree72Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block33Norm x).property (boundaryFullPowerDegree72Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block33Norm,boundaryFullPowerDegree72Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x))=c} := by

  have he : ((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x))=(boundaryImPowerRow77_18Degree72Norm x).val+(boundaryImPowerRow77_19Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree72Norm x).property (boundaryImPowerRow77_19Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree72Norm,boundaryImPowerRow77_19Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x))))=(boundaryImPowerRow77_17Degree72Norm x).val+(boundaryFullPowerDegree72Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree72Norm x).property (boundaryFullPowerDegree72Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree72Norm,boundaryFullPowerDegree72Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))=c} := by

  have he : ((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))=(boundaryImPowerRow77_21Degree72Norm x).val+(boundaryLowPowerRow77Degree72Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree72Norm x).property (boundaryLowPowerRow77Degree72Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree72Norm,boundaryLowPowerRow77Degree72Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))=(boundaryImPowerRow77_20Degree72Norm x).val+(boundaryFullPowerDegree72Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree72Norm x).property (boundaryFullPowerDegree72Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree72Norm,boundaryFullPowerDegree72Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))=(boundaryFullPowerDegree72Block38Norm x).val+(boundaryFullPowerDegree72Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block38Norm x).property (boundaryFullPowerDegree72Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block38Norm,boundaryFullPowerDegree72Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))))=(boundaryFullPowerDegree72Block36Norm x).val+(boundaryFullPowerDegree72Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block36Norm x).property (boundaryFullPowerDegree72Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block36Norm,boundaryFullPowerDegree72Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x)))))))))+(((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x)))))))))+(((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))))))=(boundaryFullPowerDegree72Block31Norm x).val+(boundaryFullPowerDegree72Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block31Norm x).property (boundaryFullPowerDegree72Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block31Norm,boundaryFullPowerDegree72Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree72Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x)))))))))+(((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x)))))))))))+(((((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x)))))))))+(((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x)))))))))+(((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x)))))))))))+(((((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x)))))))))+(((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x))))))))))))=(boundaryFullPowerDegree72Block21Norm x).val+(boundaryFullPowerDegree72Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree72Block21Norm x).property (boundaryFullPowerDegree72Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block21Norm,boundaryFullPowerDegree72Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree72Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 72 x=c} := by

  have he0 : boundaryFullPowerRow77 72 x=((((((((((boundaryRePowerRow77_0 72 x)+(boundaryRePowerRow77_1 72 x)))+(((boundaryRePowerRow77_2 72 x)+(((boundaryRePowerRow77_3 72 x)+(boundaryRePowerRow77_4 72 x)))))))+(((((boundaryRePowerRow77_5 72 x)+(((boundaryRePowerRow77_6 72 x)+(boundaryRePowerRow77_7 72 x)))))+(((boundaryRePowerRow77_8 72 x)+(((boundaryRePowerRow77_9 72 x)+(boundaryRePowerRow77_10 72 x)))))))))+(((((((boundaryRePowerRow77_11 72 x)+(((boundaryRePowerRow77_12 72 x)+(boundaryRePowerRow77_13 72 x)))))+(((boundaryRePowerRow77_14 72 x)+(((boundaryRePowerRow77_15 72 x)+(boundaryRePowerRow77_16 72 x)))))))+(((((boundaryRePowerRow77_17 72 x)+(((boundaryRePowerRow77_18 72 x)+(boundaryRePowerRow77_19 72 x)))))+(((boundaryRePowerRow77_20 72 x)+(((boundaryRePowerRow77_21 72 x)+(boundaryRePowerRow77_22 72 x)))))))))))+(((((((((boundaryImPowerRow77_0 72 x)+(boundaryImPowerRow77_1 72 x)))+(((boundaryImPowerRow77_2 72 x)+(((boundaryImPowerRow77_3 72 x)+(boundaryImPowerRow77_4 72 x)))))))+(((((boundaryImPowerRow77_5 72 x)+(((boundaryImPowerRow77_6 72 x)+(boundaryImPowerRow77_7 72 x)))))+(((boundaryImPowerRow77_8 72 x)+(((boundaryImPowerRow77_9 72 x)+(boundaryImPowerRow77_10 72 x)))))))))+(((((((boundaryImPowerRow77_11 72 x)+(((boundaryImPowerRow77_12 72 x)+(boundaryImPowerRow77_13 72 x)))))+(((boundaryImPowerRow77_14 72 x)+(((boundaryImPowerRow77_15 72 x)+(boundaryImPowerRow77_16 72 x)))))))+(((((boundaryImPowerRow77_17 72 x)+(((boundaryImPowerRow77_18 72 x)+(boundaryImPowerRow77_19 72 x)))))+(((boundaryImPowerRow77_20 72 x)+(((boundaryImPowerRow77_21 72 x)+(boundaryLowPowerRow77 72 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree72Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree72Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
