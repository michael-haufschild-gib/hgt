import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree60Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree60Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x))=c} := by

  have he : ((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x))=(boundaryRePowerRow77_0Degree60Norm x).val+(boundaryRePowerRow77_1Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree60Norm x).property (boundaryRePowerRow77_1Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree60Norm,boundaryRePowerRow77_1Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x))=c} := by

  have he : ((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x))=(boundaryRePowerRow77_3Degree60Norm x).val+(boundaryRePowerRow77_4Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree60Norm x).property (boundaryRePowerRow77_4Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree60Norm,boundaryRePowerRow77_4Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x))))=(boundaryRePowerRow77_2Degree60Norm x).val+(boundaryFullPowerDegree60Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree60Norm x).property (boundaryFullPowerDegree60Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree60Norm,boundaryFullPowerDegree60Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x))))))=(boundaryFullPowerDegree60Block0Norm x).val+(boundaryFullPowerDegree60Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block0Norm x).property (boundaryFullPowerDegree60Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block0Norm,boundaryFullPowerDegree60Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x))=c} := by

  have he : ((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x))=(boundaryRePowerRow77_6Degree60Norm x).val+(boundaryRePowerRow77_7Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree60Norm x).property (boundaryRePowerRow77_7Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree60Norm,boundaryRePowerRow77_7Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x))))=(boundaryRePowerRow77_5Degree60Norm x).val+(boundaryFullPowerDegree60Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree60Norm x).property (boundaryFullPowerDegree60Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree60Norm,boundaryFullPowerDegree60Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))=c} := by

  have he : ((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))=(boundaryRePowerRow77_9Degree60Norm x).val+(boundaryRePowerRow77_10Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree60Norm x).property (boundaryRePowerRow77_10Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree60Norm,boundaryRePowerRow77_10Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))))=(boundaryRePowerRow77_8Degree60Norm x).val+(boundaryFullPowerDegree60Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree60Norm x).property (boundaryFullPowerDegree60Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree60Norm,boundaryFullPowerDegree60Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))))))=(boundaryFullPowerDegree60Block5Norm x).val+(boundaryFullPowerDegree60Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block5Norm x).property (boundaryFullPowerDegree60Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block5Norm,boundaryFullPowerDegree60Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x))))))))=(boundaryFullPowerDegree60Block3Norm x).val+(boundaryFullPowerDegree60Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block3Norm x).property (boundaryFullPowerDegree60Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block3Norm,boundaryFullPowerDegree60Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x))=c} := by

  have he : ((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x))=(boundaryRePowerRow77_12Degree60Norm x).val+(boundaryRePowerRow77_13Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree60Norm x).property (boundaryRePowerRow77_13Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree60Norm,boundaryRePowerRow77_13Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x))))=(boundaryRePowerRow77_11Degree60Norm x).val+(boundaryFullPowerDegree60Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree60Norm x).property (boundaryFullPowerDegree60Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree60Norm,boundaryFullPowerDegree60Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x))=c} := by

  have he : ((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x))=(boundaryRePowerRow77_15Degree60Norm x).val+(boundaryRePowerRow77_16Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree60Norm x).property (boundaryRePowerRow77_16Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree60Norm,boundaryRePowerRow77_16Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x))))=(boundaryRePowerRow77_14Degree60Norm x).val+(boundaryFullPowerDegree60Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree60Norm x).property (boundaryFullPowerDegree60Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree60Norm,boundaryFullPowerDegree60Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x))))))=(boundaryFullPowerDegree60Block11Norm x).val+(boundaryFullPowerDegree60Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block11Norm x).property (boundaryFullPowerDegree60Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block11Norm,boundaryFullPowerDegree60Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x))=c} := by

  have he : ((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x))=(boundaryRePowerRow77_18Degree60Norm x).val+(boundaryRePowerRow77_19Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree60Norm x).property (boundaryRePowerRow77_19Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree60Norm,boundaryRePowerRow77_19Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x))))=(boundaryRePowerRow77_17Degree60Norm x).val+(boundaryFullPowerDegree60Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree60Norm x).property (boundaryFullPowerDegree60Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree60Norm,boundaryFullPowerDegree60Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))=c} := by

  have he : ((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))=(boundaryRePowerRow77_21Degree60Norm x).val+(boundaryRePowerRow77_22Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree60Norm x).property (boundaryRePowerRow77_22Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree60Norm,boundaryRePowerRow77_22Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))=(boundaryRePowerRow77_20Degree60Norm x).val+(boundaryFullPowerDegree60Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree60Norm x).property (boundaryFullPowerDegree60Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree60Norm,boundaryFullPowerDegree60Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))))=(boundaryFullPowerDegree60Block16Norm x).val+(boundaryFullPowerDegree60Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block16Norm x).property (boundaryFullPowerDegree60Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block16Norm,boundaryFullPowerDegree60Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))))))=(boundaryFullPowerDegree60Block14Norm x).val+(boundaryFullPowerDegree60Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block14Norm x).property (boundaryFullPowerDegree60Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block14Norm,boundaryFullPowerDegree60Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x)))))))))+(((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x)))))))))+(((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x))))))))))=(boundaryFullPowerDegree60Block9Norm x).val+(boundaryFullPowerDegree60Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block9Norm x).property (boundaryFullPowerDegree60Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block9Norm,boundaryFullPowerDegree60Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x))=c} := by

  have he : ((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x))=(boundaryImPowerRow77_0Degree60Norm x).val+(boundaryImPowerRow77_1Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree60Norm x).property (boundaryImPowerRow77_1Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree60Norm,boundaryImPowerRow77_1Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x))=c} := by

  have he : ((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x))=(boundaryImPowerRow77_3Degree60Norm x).val+(boundaryImPowerRow77_4Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree60Norm x).property (boundaryImPowerRow77_4Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree60Norm,boundaryImPowerRow77_4Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x))))=(boundaryImPowerRow77_2Degree60Norm x).val+(boundaryFullPowerDegree60Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree60Norm x).property (boundaryFullPowerDegree60Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree60Norm,boundaryFullPowerDegree60Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x))))))=(boundaryFullPowerDegree60Block22Norm x).val+(boundaryFullPowerDegree60Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block22Norm x).property (boundaryFullPowerDegree60Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block22Norm,boundaryFullPowerDegree60Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x))=c} := by

  have he : ((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x))=(boundaryImPowerRow77_6Degree60Norm x).val+(boundaryImPowerRow77_7Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree60Norm x).property (boundaryImPowerRow77_7Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree60Norm,boundaryImPowerRow77_7Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x))))=(boundaryImPowerRow77_5Degree60Norm x).val+(boundaryFullPowerDegree60Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree60Norm x).property (boundaryFullPowerDegree60Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree60Norm,boundaryFullPowerDegree60Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))=c} := by

  have he : ((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))=(boundaryImPowerRow77_9Degree60Norm x).val+(boundaryImPowerRow77_10Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree60Norm x).property (boundaryImPowerRow77_10Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree60Norm,boundaryImPowerRow77_10Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))))=(boundaryImPowerRow77_8Degree60Norm x).val+(boundaryFullPowerDegree60Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree60Norm x).property (boundaryFullPowerDegree60Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree60Norm,boundaryFullPowerDegree60Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))))))=(boundaryFullPowerDegree60Block27Norm x).val+(boundaryFullPowerDegree60Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block27Norm x).property (boundaryFullPowerDegree60Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block27Norm,boundaryFullPowerDegree60Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x))))))))=(boundaryFullPowerDegree60Block25Norm x).val+(boundaryFullPowerDegree60Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block25Norm x).property (boundaryFullPowerDegree60Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block25Norm,boundaryFullPowerDegree60Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x))=c} := by

  have he : ((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x))=(boundaryImPowerRow77_12Degree60Norm x).val+(boundaryImPowerRow77_13Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree60Norm x).property (boundaryImPowerRow77_13Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree60Norm,boundaryImPowerRow77_13Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x))))=(boundaryImPowerRow77_11Degree60Norm x).val+(boundaryFullPowerDegree60Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree60Norm x).property (boundaryFullPowerDegree60Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree60Norm,boundaryFullPowerDegree60Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x))=c} := by

  have he : ((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x))=(boundaryImPowerRow77_15Degree60Norm x).val+(boundaryImPowerRow77_16Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree60Norm x).property (boundaryImPowerRow77_16Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree60Norm,boundaryImPowerRow77_16Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x))))=(boundaryImPowerRow77_14Degree60Norm x).val+(boundaryFullPowerDegree60Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree60Norm x).property (boundaryFullPowerDegree60Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree60Norm,boundaryFullPowerDegree60Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x))))))=(boundaryFullPowerDegree60Block33Norm x).val+(boundaryFullPowerDegree60Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block33Norm x).property (boundaryFullPowerDegree60Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block33Norm,boundaryFullPowerDegree60Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x))=c} := by

  have he : ((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x))=(boundaryImPowerRow77_18Degree60Norm x).val+(boundaryImPowerRow77_19Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree60Norm x).property (boundaryImPowerRow77_19Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree60Norm,boundaryImPowerRow77_19Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x))))=(boundaryImPowerRow77_17Degree60Norm x).val+(boundaryFullPowerDegree60Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree60Norm x).property (boundaryFullPowerDegree60Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree60Norm,boundaryFullPowerDegree60Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))=c} := by

  have he : ((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))=(boundaryImPowerRow77_21Degree60Norm x).val+(boundaryLowPowerRow77Degree60Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree60Norm x).property (boundaryLowPowerRow77Degree60Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree60Norm,boundaryLowPowerRow77Degree60Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))=(boundaryImPowerRow77_20Degree60Norm x).val+(boundaryFullPowerDegree60Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree60Norm x).property (boundaryFullPowerDegree60Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree60Norm,boundaryFullPowerDegree60Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))=(boundaryFullPowerDegree60Block38Norm x).val+(boundaryFullPowerDegree60Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block38Norm x).property (boundaryFullPowerDegree60Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block38Norm,boundaryFullPowerDegree60Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))))=(boundaryFullPowerDegree60Block36Norm x).val+(boundaryFullPowerDegree60Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block36Norm x).property (boundaryFullPowerDegree60Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block36Norm,boundaryFullPowerDegree60Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x)))))))))+(((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x)))))))))+(((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))))))=(boundaryFullPowerDegree60Block31Norm x).val+(boundaryFullPowerDegree60Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block31Norm x).property (boundaryFullPowerDegree60Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block31Norm,boundaryFullPowerDegree60Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree60Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x)))))))))+(((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x)))))))))))+(((((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x)))))))))+(((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x)))))))))+(((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x)))))))))))+(((((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x)))))))))+(((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x))))))))))))=(boundaryFullPowerDegree60Block21Norm x).val+(boundaryFullPowerDegree60Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree60Block21Norm x).property (boundaryFullPowerDegree60Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block21Norm,boundaryFullPowerDegree60Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree60Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 60 x=c} := by

  have he0 : boundaryFullPowerRow77 60 x=((((((((((boundaryRePowerRow77_0 60 x)+(boundaryRePowerRow77_1 60 x)))+(((boundaryRePowerRow77_2 60 x)+(((boundaryRePowerRow77_3 60 x)+(boundaryRePowerRow77_4 60 x)))))))+(((((boundaryRePowerRow77_5 60 x)+(((boundaryRePowerRow77_6 60 x)+(boundaryRePowerRow77_7 60 x)))))+(((boundaryRePowerRow77_8 60 x)+(((boundaryRePowerRow77_9 60 x)+(boundaryRePowerRow77_10 60 x)))))))))+(((((((boundaryRePowerRow77_11 60 x)+(((boundaryRePowerRow77_12 60 x)+(boundaryRePowerRow77_13 60 x)))))+(((boundaryRePowerRow77_14 60 x)+(((boundaryRePowerRow77_15 60 x)+(boundaryRePowerRow77_16 60 x)))))))+(((((boundaryRePowerRow77_17 60 x)+(((boundaryRePowerRow77_18 60 x)+(boundaryRePowerRow77_19 60 x)))))+(((boundaryRePowerRow77_20 60 x)+(((boundaryRePowerRow77_21 60 x)+(boundaryRePowerRow77_22 60 x)))))))))))+(((((((((boundaryImPowerRow77_0 60 x)+(boundaryImPowerRow77_1 60 x)))+(((boundaryImPowerRow77_2 60 x)+(((boundaryImPowerRow77_3 60 x)+(boundaryImPowerRow77_4 60 x)))))))+(((((boundaryImPowerRow77_5 60 x)+(((boundaryImPowerRow77_6 60 x)+(boundaryImPowerRow77_7 60 x)))))+(((boundaryImPowerRow77_8 60 x)+(((boundaryImPowerRow77_9 60 x)+(boundaryImPowerRow77_10 60 x)))))))))+(((((((boundaryImPowerRow77_11 60 x)+(((boundaryImPowerRow77_12 60 x)+(boundaryImPowerRow77_13 60 x)))))+(((boundaryImPowerRow77_14 60 x)+(((boundaryImPowerRow77_15 60 x)+(boundaryImPowerRow77_16 60 x)))))))+(((((boundaryImPowerRow77_17 60 x)+(((boundaryImPowerRow77_18 60 x)+(boundaryImPowerRow77_19 60 x)))))+(((boundaryImPowerRow77_20 60 x)+(((boundaryImPowerRow77_21 60 x)+(boundaryLowPowerRow77 60 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree60Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree60Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
