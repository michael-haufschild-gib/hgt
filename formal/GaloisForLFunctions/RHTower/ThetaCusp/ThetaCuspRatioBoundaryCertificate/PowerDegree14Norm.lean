import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree14Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree14Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x))=c} := by

  have he : ((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x))=(boundaryRePowerRow77_0Degree14Norm x).val+(boundaryRePowerRow77_1Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree14Norm x).property (boundaryRePowerRow77_1Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree14Norm,boundaryRePowerRow77_1Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x))=c} := by

  have he : ((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x))=(boundaryRePowerRow77_3Degree14Norm x).val+(boundaryRePowerRow77_4Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree14Norm x).property (boundaryRePowerRow77_4Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree14Norm,boundaryRePowerRow77_4Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x))))=(boundaryRePowerRow77_2Degree14Norm x).val+(boundaryFullPowerDegree14Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree14Norm x).property (boundaryFullPowerDegree14Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree14Norm,boundaryFullPowerDegree14Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x))))))=(boundaryFullPowerDegree14Block0Norm x).val+(boundaryFullPowerDegree14Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block0Norm x).property (boundaryFullPowerDegree14Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block0Norm,boundaryFullPowerDegree14Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x))=c} := by

  have he : ((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x))=(boundaryRePowerRow77_6Degree14Norm x).val+(boundaryRePowerRow77_7Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree14Norm x).property (boundaryRePowerRow77_7Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree14Norm,boundaryRePowerRow77_7Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x))))=(boundaryRePowerRow77_5Degree14Norm x).val+(boundaryFullPowerDegree14Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree14Norm x).property (boundaryFullPowerDegree14Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree14Norm,boundaryFullPowerDegree14Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))=c} := by

  have he : ((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))=(boundaryRePowerRow77_9Degree14Norm x).val+(boundaryRePowerRow77_10Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree14Norm x).property (boundaryRePowerRow77_10Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree14Norm,boundaryRePowerRow77_10Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))))=(boundaryRePowerRow77_8Degree14Norm x).val+(boundaryFullPowerDegree14Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree14Norm x).property (boundaryFullPowerDegree14Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree14Norm,boundaryFullPowerDegree14Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))))))=(boundaryFullPowerDegree14Block5Norm x).val+(boundaryFullPowerDegree14Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block5Norm x).property (boundaryFullPowerDegree14Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block5Norm,boundaryFullPowerDegree14Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x))))))))=(boundaryFullPowerDegree14Block3Norm x).val+(boundaryFullPowerDegree14Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block3Norm x).property (boundaryFullPowerDegree14Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block3Norm,boundaryFullPowerDegree14Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x))=c} := by

  have he : ((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x))=(boundaryRePowerRow77_12Degree14Norm x).val+(boundaryRePowerRow77_13Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree14Norm x).property (boundaryRePowerRow77_13Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree14Norm,boundaryRePowerRow77_13Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x))))=(boundaryRePowerRow77_11Degree14Norm x).val+(boundaryFullPowerDegree14Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree14Norm x).property (boundaryFullPowerDegree14Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree14Norm,boundaryFullPowerDegree14Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x))=c} := by

  have he : ((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x))=(boundaryRePowerRow77_15Degree14Norm x).val+(boundaryRePowerRow77_16Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree14Norm x).property (boundaryRePowerRow77_16Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree14Norm,boundaryRePowerRow77_16Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x))))=(boundaryRePowerRow77_14Degree14Norm x).val+(boundaryFullPowerDegree14Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree14Norm x).property (boundaryFullPowerDegree14Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree14Norm,boundaryFullPowerDegree14Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x))))))=(boundaryFullPowerDegree14Block11Norm x).val+(boundaryFullPowerDegree14Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block11Norm x).property (boundaryFullPowerDegree14Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block11Norm,boundaryFullPowerDegree14Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x))=c} := by

  have he : ((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x))=(boundaryRePowerRow77_18Degree14Norm x).val+(boundaryRePowerRow77_19Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree14Norm x).property (boundaryRePowerRow77_19Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree14Norm,boundaryRePowerRow77_19Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x))))=(boundaryRePowerRow77_17Degree14Norm x).val+(boundaryFullPowerDegree14Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree14Norm x).property (boundaryFullPowerDegree14Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree14Norm,boundaryFullPowerDegree14Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))=c} := by

  have he : ((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))=(boundaryRePowerRow77_21Degree14Norm x).val+(boundaryRePowerRow77_22Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree14Norm x).property (boundaryRePowerRow77_22Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree14Norm,boundaryRePowerRow77_22Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))=(boundaryRePowerRow77_20Degree14Norm x).val+(boundaryFullPowerDegree14Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree14Norm x).property (boundaryFullPowerDegree14Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree14Norm,boundaryFullPowerDegree14Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))))=(boundaryFullPowerDegree14Block16Norm x).val+(boundaryFullPowerDegree14Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block16Norm x).property (boundaryFullPowerDegree14Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block16Norm,boundaryFullPowerDegree14Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))))))=(boundaryFullPowerDegree14Block14Norm x).val+(boundaryFullPowerDegree14Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block14Norm x).property (boundaryFullPowerDegree14Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block14Norm,boundaryFullPowerDegree14Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x)))))))))+(((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x)))))))))+(((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x))))))))))=(boundaryFullPowerDegree14Block9Norm x).val+(boundaryFullPowerDegree14Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block9Norm x).property (boundaryFullPowerDegree14Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block9Norm,boundaryFullPowerDegree14Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x))=c} := by

  have he : ((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x))=(boundaryImPowerRow77_0Degree14Norm x).val+(boundaryImPowerRow77_1Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree14Norm x).property (boundaryImPowerRow77_1Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree14Norm,boundaryImPowerRow77_1Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x))=c} := by

  have he : ((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x))=(boundaryImPowerRow77_3Degree14Norm x).val+(boundaryImPowerRow77_4Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree14Norm x).property (boundaryImPowerRow77_4Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree14Norm,boundaryImPowerRow77_4Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x))))=(boundaryImPowerRow77_2Degree14Norm x).val+(boundaryFullPowerDegree14Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree14Norm x).property (boundaryFullPowerDegree14Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree14Norm,boundaryFullPowerDegree14Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x))))))=(boundaryFullPowerDegree14Block22Norm x).val+(boundaryFullPowerDegree14Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block22Norm x).property (boundaryFullPowerDegree14Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block22Norm,boundaryFullPowerDegree14Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x))=c} := by

  have he : ((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x))=(boundaryImPowerRow77_6Degree14Norm x).val+(boundaryImPowerRow77_7Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree14Norm x).property (boundaryImPowerRow77_7Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree14Norm,boundaryImPowerRow77_7Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x))))=(boundaryImPowerRow77_5Degree14Norm x).val+(boundaryFullPowerDegree14Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree14Norm x).property (boundaryFullPowerDegree14Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree14Norm,boundaryFullPowerDegree14Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))=c} := by

  have he : ((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))=(boundaryImPowerRow77_9Degree14Norm x).val+(boundaryImPowerRow77_10Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree14Norm x).property (boundaryImPowerRow77_10Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree14Norm,boundaryImPowerRow77_10Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))))=(boundaryImPowerRow77_8Degree14Norm x).val+(boundaryFullPowerDegree14Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree14Norm x).property (boundaryFullPowerDegree14Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree14Norm,boundaryFullPowerDegree14Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))))))=(boundaryFullPowerDegree14Block27Norm x).val+(boundaryFullPowerDegree14Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block27Norm x).property (boundaryFullPowerDegree14Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block27Norm,boundaryFullPowerDegree14Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x))))))))=(boundaryFullPowerDegree14Block25Norm x).val+(boundaryFullPowerDegree14Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block25Norm x).property (boundaryFullPowerDegree14Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block25Norm,boundaryFullPowerDegree14Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x))=c} := by

  have he : ((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x))=(boundaryImPowerRow77_12Degree14Norm x).val+(boundaryImPowerRow77_13Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree14Norm x).property (boundaryImPowerRow77_13Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree14Norm,boundaryImPowerRow77_13Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x))))=(boundaryImPowerRow77_11Degree14Norm x).val+(boundaryFullPowerDegree14Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree14Norm x).property (boundaryFullPowerDegree14Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree14Norm,boundaryFullPowerDegree14Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x))=c} := by

  have he : ((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x))=(boundaryImPowerRow77_15Degree14Norm x).val+(boundaryImPowerRow77_16Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree14Norm x).property (boundaryImPowerRow77_16Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree14Norm,boundaryImPowerRow77_16Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x))))=(boundaryImPowerRow77_14Degree14Norm x).val+(boundaryFullPowerDegree14Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree14Norm x).property (boundaryFullPowerDegree14Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree14Norm,boundaryFullPowerDegree14Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x))))))=(boundaryFullPowerDegree14Block33Norm x).val+(boundaryFullPowerDegree14Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block33Norm x).property (boundaryFullPowerDegree14Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block33Norm,boundaryFullPowerDegree14Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x))=c} := by

  have he : ((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x))=(boundaryImPowerRow77_18Degree14Norm x).val+(boundaryImPowerRow77_19Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree14Norm x).property (boundaryImPowerRow77_19Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree14Norm,boundaryImPowerRow77_19Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x))))=(boundaryImPowerRow77_17Degree14Norm x).val+(boundaryFullPowerDegree14Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree14Norm x).property (boundaryFullPowerDegree14Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree14Norm,boundaryFullPowerDegree14Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))=c} := by

  have he : ((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))=(boundaryImPowerRow77_21Degree14Norm x).val+(boundaryLowPowerRow77Degree14Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree14Norm x).property (boundaryLowPowerRow77Degree14Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree14Norm,boundaryLowPowerRow77Degree14Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))=(boundaryImPowerRow77_20Degree14Norm x).val+(boundaryFullPowerDegree14Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree14Norm x).property (boundaryFullPowerDegree14Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree14Norm,boundaryFullPowerDegree14Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))=(boundaryFullPowerDegree14Block38Norm x).val+(boundaryFullPowerDegree14Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block38Norm x).property (boundaryFullPowerDegree14Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block38Norm,boundaryFullPowerDegree14Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))))=(boundaryFullPowerDegree14Block36Norm x).val+(boundaryFullPowerDegree14Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block36Norm x).property (boundaryFullPowerDegree14Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block36Norm,boundaryFullPowerDegree14Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x)))))))))+(((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x)))))))))+(((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))))))=(boundaryFullPowerDegree14Block31Norm x).val+(boundaryFullPowerDegree14Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block31Norm x).property (boundaryFullPowerDegree14Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block31Norm,boundaryFullPowerDegree14Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree14Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x)))))))))+(((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x)))))))))))+(((((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x)))))))))+(((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x)))))))))+(((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x)))))))))))+(((((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x)))))))))+(((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x))))))))))))=(boundaryFullPowerDegree14Block21Norm x).val+(boundaryFullPowerDegree14Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree14Block21Norm x).property (boundaryFullPowerDegree14Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block21Norm,boundaryFullPowerDegree14Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree14Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 14 x=c} := by

  have he0 : boundaryFullPowerRow77 14 x=((((((((((boundaryRePowerRow77_0 14 x)+(boundaryRePowerRow77_1 14 x)))+(((boundaryRePowerRow77_2 14 x)+(((boundaryRePowerRow77_3 14 x)+(boundaryRePowerRow77_4 14 x)))))))+(((((boundaryRePowerRow77_5 14 x)+(((boundaryRePowerRow77_6 14 x)+(boundaryRePowerRow77_7 14 x)))))+(((boundaryRePowerRow77_8 14 x)+(((boundaryRePowerRow77_9 14 x)+(boundaryRePowerRow77_10 14 x)))))))))+(((((((boundaryRePowerRow77_11 14 x)+(((boundaryRePowerRow77_12 14 x)+(boundaryRePowerRow77_13 14 x)))))+(((boundaryRePowerRow77_14 14 x)+(((boundaryRePowerRow77_15 14 x)+(boundaryRePowerRow77_16 14 x)))))))+(((((boundaryRePowerRow77_17 14 x)+(((boundaryRePowerRow77_18 14 x)+(boundaryRePowerRow77_19 14 x)))))+(((boundaryRePowerRow77_20 14 x)+(((boundaryRePowerRow77_21 14 x)+(boundaryRePowerRow77_22 14 x)))))))))))+(((((((((boundaryImPowerRow77_0 14 x)+(boundaryImPowerRow77_1 14 x)))+(((boundaryImPowerRow77_2 14 x)+(((boundaryImPowerRow77_3 14 x)+(boundaryImPowerRow77_4 14 x)))))))+(((((boundaryImPowerRow77_5 14 x)+(((boundaryImPowerRow77_6 14 x)+(boundaryImPowerRow77_7 14 x)))))+(((boundaryImPowerRow77_8 14 x)+(((boundaryImPowerRow77_9 14 x)+(boundaryImPowerRow77_10 14 x)))))))))+(((((((boundaryImPowerRow77_11 14 x)+(((boundaryImPowerRow77_12 14 x)+(boundaryImPowerRow77_13 14 x)))))+(((boundaryImPowerRow77_14 14 x)+(((boundaryImPowerRow77_15 14 x)+(boundaryImPowerRow77_16 14 x)))))))+(((((boundaryImPowerRow77_17 14 x)+(((boundaryImPowerRow77_18 14 x)+(boundaryImPowerRow77_19 14 x)))))+(((boundaryImPowerRow77_20 14 x)+(((boundaryImPowerRow77_21 14 x)+(boundaryLowPowerRow77 14 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree14Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree14Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
