import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree31Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree31Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x))=c} := by

  have he : ((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x))=(boundaryRePowerRow77_0Degree31Norm x).val+(boundaryRePowerRow77_1Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree31Norm x).property (boundaryRePowerRow77_1Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree31Norm,boundaryRePowerRow77_1Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x))=c} := by

  have he : ((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x))=(boundaryRePowerRow77_3Degree31Norm x).val+(boundaryRePowerRow77_4Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree31Norm x).property (boundaryRePowerRow77_4Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree31Norm,boundaryRePowerRow77_4Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x))))=(boundaryRePowerRow77_2Degree31Norm x).val+(boundaryFullPowerDegree31Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree31Norm x).property (boundaryFullPowerDegree31Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree31Norm,boundaryFullPowerDegree31Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x))))))=(boundaryFullPowerDegree31Block0Norm x).val+(boundaryFullPowerDegree31Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block0Norm x).property (boundaryFullPowerDegree31Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block0Norm,boundaryFullPowerDegree31Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x))=c} := by

  have he : ((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x))=(boundaryRePowerRow77_6Degree31Norm x).val+(boundaryRePowerRow77_7Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree31Norm x).property (boundaryRePowerRow77_7Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree31Norm,boundaryRePowerRow77_7Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x))))=(boundaryRePowerRow77_5Degree31Norm x).val+(boundaryFullPowerDegree31Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree31Norm x).property (boundaryFullPowerDegree31Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree31Norm,boundaryFullPowerDegree31Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))=c} := by

  have he : ((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))=(boundaryRePowerRow77_9Degree31Norm x).val+(boundaryRePowerRow77_10Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree31Norm x).property (boundaryRePowerRow77_10Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree31Norm,boundaryRePowerRow77_10Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))))=(boundaryRePowerRow77_8Degree31Norm x).val+(boundaryFullPowerDegree31Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree31Norm x).property (boundaryFullPowerDegree31Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree31Norm,boundaryFullPowerDegree31Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))))))=(boundaryFullPowerDegree31Block5Norm x).val+(boundaryFullPowerDegree31Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block5Norm x).property (boundaryFullPowerDegree31Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block5Norm,boundaryFullPowerDegree31Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x))))))))=(boundaryFullPowerDegree31Block3Norm x).val+(boundaryFullPowerDegree31Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block3Norm x).property (boundaryFullPowerDegree31Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block3Norm,boundaryFullPowerDegree31Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x))=c} := by

  have he : ((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x))=(boundaryRePowerRow77_12Degree31Norm x).val+(boundaryRePowerRow77_13Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree31Norm x).property (boundaryRePowerRow77_13Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree31Norm,boundaryRePowerRow77_13Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x))))=(boundaryRePowerRow77_11Degree31Norm x).val+(boundaryFullPowerDegree31Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree31Norm x).property (boundaryFullPowerDegree31Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree31Norm,boundaryFullPowerDegree31Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x))=c} := by

  have he : ((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x))=(boundaryRePowerRow77_15Degree31Norm x).val+(boundaryRePowerRow77_16Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree31Norm x).property (boundaryRePowerRow77_16Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree31Norm,boundaryRePowerRow77_16Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x))))=(boundaryRePowerRow77_14Degree31Norm x).val+(boundaryFullPowerDegree31Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree31Norm x).property (boundaryFullPowerDegree31Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree31Norm,boundaryFullPowerDegree31Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x))))))=(boundaryFullPowerDegree31Block11Norm x).val+(boundaryFullPowerDegree31Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block11Norm x).property (boundaryFullPowerDegree31Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block11Norm,boundaryFullPowerDegree31Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x))=c} := by

  have he : ((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x))=(boundaryRePowerRow77_18Degree31Norm x).val+(boundaryRePowerRow77_19Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree31Norm x).property (boundaryRePowerRow77_19Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree31Norm,boundaryRePowerRow77_19Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x))))=(boundaryRePowerRow77_17Degree31Norm x).val+(boundaryFullPowerDegree31Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree31Norm x).property (boundaryFullPowerDegree31Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree31Norm,boundaryFullPowerDegree31Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))=c} := by

  have he : ((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))=(boundaryRePowerRow77_21Degree31Norm x).val+(boundaryRePowerRow77_22Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree31Norm x).property (boundaryRePowerRow77_22Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree31Norm,boundaryRePowerRow77_22Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))=(boundaryRePowerRow77_20Degree31Norm x).val+(boundaryFullPowerDegree31Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree31Norm x).property (boundaryFullPowerDegree31Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree31Norm,boundaryFullPowerDegree31Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))))=(boundaryFullPowerDegree31Block16Norm x).val+(boundaryFullPowerDegree31Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block16Norm x).property (boundaryFullPowerDegree31Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block16Norm,boundaryFullPowerDegree31Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))))))=(boundaryFullPowerDegree31Block14Norm x).val+(boundaryFullPowerDegree31Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block14Norm x).property (boundaryFullPowerDegree31Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block14Norm,boundaryFullPowerDegree31Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x)))))))))+(((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x)))))))))+(((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x))))))))))=(boundaryFullPowerDegree31Block9Norm x).val+(boundaryFullPowerDegree31Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block9Norm x).property (boundaryFullPowerDegree31Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block9Norm,boundaryFullPowerDegree31Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x))=c} := by

  have he : ((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x))=(boundaryImPowerRow77_0Degree31Norm x).val+(boundaryImPowerRow77_1Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree31Norm x).property (boundaryImPowerRow77_1Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree31Norm,boundaryImPowerRow77_1Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x))=c} := by

  have he : ((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x))=(boundaryImPowerRow77_3Degree31Norm x).val+(boundaryImPowerRow77_4Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree31Norm x).property (boundaryImPowerRow77_4Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree31Norm,boundaryImPowerRow77_4Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x))))=(boundaryImPowerRow77_2Degree31Norm x).val+(boundaryFullPowerDegree31Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree31Norm x).property (boundaryFullPowerDegree31Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree31Norm,boundaryFullPowerDegree31Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x))))))=(boundaryFullPowerDegree31Block22Norm x).val+(boundaryFullPowerDegree31Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block22Norm x).property (boundaryFullPowerDegree31Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block22Norm,boundaryFullPowerDegree31Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x))=c} := by

  have he : ((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x))=(boundaryImPowerRow77_6Degree31Norm x).val+(boundaryImPowerRow77_7Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree31Norm x).property (boundaryImPowerRow77_7Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree31Norm,boundaryImPowerRow77_7Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x))))=(boundaryImPowerRow77_5Degree31Norm x).val+(boundaryFullPowerDegree31Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree31Norm x).property (boundaryFullPowerDegree31Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree31Norm,boundaryFullPowerDegree31Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))=c} := by

  have he : ((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))=(boundaryImPowerRow77_9Degree31Norm x).val+(boundaryImPowerRow77_10Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree31Norm x).property (boundaryImPowerRow77_10Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree31Norm,boundaryImPowerRow77_10Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))))=(boundaryImPowerRow77_8Degree31Norm x).val+(boundaryFullPowerDegree31Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree31Norm x).property (boundaryFullPowerDegree31Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree31Norm,boundaryFullPowerDegree31Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))))))=(boundaryFullPowerDegree31Block27Norm x).val+(boundaryFullPowerDegree31Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block27Norm x).property (boundaryFullPowerDegree31Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block27Norm,boundaryFullPowerDegree31Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x))))))))=(boundaryFullPowerDegree31Block25Norm x).val+(boundaryFullPowerDegree31Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block25Norm x).property (boundaryFullPowerDegree31Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block25Norm,boundaryFullPowerDegree31Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x))=c} := by

  have he : ((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x))=(boundaryImPowerRow77_12Degree31Norm x).val+(boundaryImPowerRow77_13Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree31Norm x).property (boundaryImPowerRow77_13Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree31Norm,boundaryImPowerRow77_13Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x))))=(boundaryImPowerRow77_11Degree31Norm x).val+(boundaryFullPowerDegree31Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree31Norm x).property (boundaryFullPowerDegree31Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree31Norm,boundaryFullPowerDegree31Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x))=c} := by

  have he : ((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x))=(boundaryImPowerRow77_15Degree31Norm x).val+(boundaryImPowerRow77_16Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree31Norm x).property (boundaryImPowerRow77_16Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree31Norm,boundaryImPowerRow77_16Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x))))=(boundaryImPowerRow77_14Degree31Norm x).val+(boundaryFullPowerDegree31Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree31Norm x).property (boundaryFullPowerDegree31Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree31Norm,boundaryFullPowerDegree31Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x))))))=(boundaryFullPowerDegree31Block33Norm x).val+(boundaryFullPowerDegree31Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block33Norm x).property (boundaryFullPowerDegree31Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block33Norm,boundaryFullPowerDegree31Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x))=c} := by

  have he : ((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x))=(boundaryImPowerRow77_18Degree31Norm x).val+(boundaryImPowerRow77_19Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree31Norm x).property (boundaryImPowerRow77_19Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree31Norm,boundaryImPowerRow77_19Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x))))=(boundaryImPowerRow77_17Degree31Norm x).val+(boundaryFullPowerDegree31Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree31Norm x).property (boundaryFullPowerDegree31Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree31Norm,boundaryFullPowerDegree31Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))=c} := by

  have he : ((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))=(boundaryImPowerRow77_21Degree31Norm x).val+(boundaryLowPowerRow77Degree31Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree31Norm x).property (boundaryLowPowerRow77Degree31Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree31Norm,boundaryLowPowerRow77Degree31Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))=(boundaryImPowerRow77_20Degree31Norm x).val+(boundaryFullPowerDegree31Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree31Norm x).property (boundaryFullPowerDegree31Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree31Norm,boundaryFullPowerDegree31Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))=(boundaryFullPowerDegree31Block38Norm x).val+(boundaryFullPowerDegree31Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block38Norm x).property (boundaryFullPowerDegree31Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block38Norm,boundaryFullPowerDegree31Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))))=(boundaryFullPowerDegree31Block36Norm x).val+(boundaryFullPowerDegree31Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block36Norm x).property (boundaryFullPowerDegree31Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block36Norm,boundaryFullPowerDegree31Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x)))))))))+(((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x)))))))))+(((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))))))=(boundaryFullPowerDegree31Block31Norm x).val+(boundaryFullPowerDegree31Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block31Norm x).property (boundaryFullPowerDegree31Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block31Norm,boundaryFullPowerDegree31Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree31Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x)))))))))+(((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x)))))))))))+(((((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x)))))))))+(((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x)))))))))+(((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x)))))))))))+(((((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x)))))))))+(((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x))))))))))))=(boundaryFullPowerDegree31Block21Norm x).val+(boundaryFullPowerDegree31Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree31Block21Norm x).property (boundaryFullPowerDegree31Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block21Norm,boundaryFullPowerDegree31Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree31Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 31 x=c} := by

  have he0 : boundaryFullPowerRow77 31 x=((((((((((boundaryRePowerRow77_0 31 x)+(boundaryRePowerRow77_1 31 x)))+(((boundaryRePowerRow77_2 31 x)+(((boundaryRePowerRow77_3 31 x)+(boundaryRePowerRow77_4 31 x)))))))+(((((boundaryRePowerRow77_5 31 x)+(((boundaryRePowerRow77_6 31 x)+(boundaryRePowerRow77_7 31 x)))))+(((boundaryRePowerRow77_8 31 x)+(((boundaryRePowerRow77_9 31 x)+(boundaryRePowerRow77_10 31 x)))))))))+(((((((boundaryRePowerRow77_11 31 x)+(((boundaryRePowerRow77_12 31 x)+(boundaryRePowerRow77_13 31 x)))))+(((boundaryRePowerRow77_14 31 x)+(((boundaryRePowerRow77_15 31 x)+(boundaryRePowerRow77_16 31 x)))))))+(((((boundaryRePowerRow77_17 31 x)+(((boundaryRePowerRow77_18 31 x)+(boundaryRePowerRow77_19 31 x)))))+(((boundaryRePowerRow77_20 31 x)+(((boundaryRePowerRow77_21 31 x)+(boundaryRePowerRow77_22 31 x)))))))))))+(((((((((boundaryImPowerRow77_0 31 x)+(boundaryImPowerRow77_1 31 x)))+(((boundaryImPowerRow77_2 31 x)+(((boundaryImPowerRow77_3 31 x)+(boundaryImPowerRow77_4 31 x)))))))+(((((boundaryImPowerRow77_5 31 x)+(((boundaryImPowerRow77_6 31 x)+(boundaryImPowerRow77_7 31 x)))))+(((boundaryImPowerRow77_8 31 x)+(((boundaryImPowerRow77_9 31 x)+(boundaryImPowerRow77_10 31 x)))))))))+(((((((boundaryImPowerRow77_11 31 x)+(((boundaryImPowerRow77_12 31 x)+(boundaryImPowerRow77_13 31 x)))))+(((boundaryImPowerRow77_14 31 x)+(((boundaryImPowerRow77_15 31 x)+(boundaryImPowerRow77_16 31 x)))))))+(((((boundaryImPowerRow77_17 31 x)+(((boundaryImPowerRow77_18 31 x)+(boundaryImPowerRow77_19 31 x)))))+(((boundaryImPowerRow77_20 31 x)+(((boundaryImPowerRow77_21 31 x)+(boundaryLowPowerRow77 31 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree31Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree31Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
