import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree63Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree63Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x))=c} := by

  have he : ((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x))=(boundaryRePowerRow77_0Degree63Norm x).val+(boundaryRePowerRow77_1Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree63Norm x).property (boundaryRePowerRow77_1Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree63Norm,boundaryRePowerRow77_1Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x))=c} := by

  have he : ((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x))=(boundaryRePowerRow77_3Degree63Norm x).val+(boundaryRePowerRow77_4Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree63Norm x).property (boundaryRePowerRow77_4Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree63Norm,boundaryRePowerRow77_4Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x))))=(boundaryRePowerRow77_2Degree63Norm x).val+(boundaryFullPowerDegree63Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree63Norm x).property (boundaryFullPowerDegree63Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree63Norm,boundaryFullPowerDegree63Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x))))))=(boundaryFullPowerDegree63Block0Norm x).val+(boundaryFullPowerDegree63Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block0Norm x).property (boundaryFullPowerDegree63Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block0Norm,boundaryFullPowerDegree63Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x))=c} := by

  have he : ((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x))=(boundaryRePowerRow77_6Degree63Norm x).val+(boundaryRePowerRow77_7Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree63Norm x).property (boundaryRePowerRow77_7Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree63Norm,boundaryRePowerRow77_7Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x))))=(boundaryRePowerRow77_5Degree63Norm x).val+(boundaryFullPowerDegree63Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree63Norm x).property (boundaryFullPowerDegree63Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree63Norm,boundaryFullPowerDegree63Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))=c} := by

  have he : ((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))=(boundaryRePowerRow77_9Degree63Norm x).val+(boundaryRePowerRow77_10Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree63Norm x).property (boundaryRePowerRow77_10Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree63Norm,boundaryRePowerRow77_10Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))))=(boundaryRePowerRow77_8Degree63Norm x).val+(boundaryFullPowerDegree63Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree63Norm x).property (boundaryFullPowerDegree63Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree63Norm,boundaryFullPowerDegree63Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))))))=(boundaryFullPowerDegree63Block5Norm x).val+(boundaryFullPowerDegree63Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block5Norm x).property (boundaryFullPowerDegree63Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block5Norm,boundaryFullPowerDegree63Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x))))))))=(boundaryFullPowerDegree63Block3Norm x).val+(boundaryFullPowerDegree63Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block3Norm x).property (boundaryFullPowerDegree63Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block3Norm,boundaryFullPowerDegree63Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x))=c} := by

  have he : ((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x))=(boundaryRePowerRow77_12Degree63Norm x).val+(boundaryRePowerRow77_13Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree63Norm x).property (boundaryRePowerRow77_13Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree63Norm,boundaryRePowerRow77_13Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x))))=(boundaryRePowerRow77_11Degree63Norm x).val+(boundaryFullPowerDegree63Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree63Norm x).property (boundaryFullPowerDegree63Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree63Norm,boundaryFullPowerDegree63Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x))=c} := by

  have he : ((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x))=(boundaryRePowerRow77_15Degree63Norm x).val+(boundaryRePowerRow77_16Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree63Norm x).property (boundaryRePowerRow77_16Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree63Norm,boundaryRePowerRow77_16Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x))))=(boundaryRePowerRow77_14Degree63Norm x).val+(boundaryFullPowerDegree63Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree63Norm x).property (boundaryFullPowerDegree63Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree63Norm,boundaryFullPowerDegree63Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x))))))=(boundaryFullPowerDegree63Block11Norm x).val+(boundaryFullPowerDegree63Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block11Norm x).property (boundaryFullPowerDegree63Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block11Norm,boundaryFullPowerDegree63Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x))=c} := by

  have he : ((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x))=(boundaryRePowerRow77_18Degree63Norm x).val+(boundaryRePowerRow77_19Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree63Norm x).property (boundaryRePowerRow77_19Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree63Norm,boundaryRePowerRow77_19Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x))))=(boundaryRePowerRow77_17Degree63Norm x).val+(boundaryFullPowerDegree63Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree63Norm x).property (boundaryFullPowerDegree63Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree63Norm,boundaryFullPowerDegree63Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))=c} := by

  have he : ((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))=(boundaryRePowerRow77_21Degree63Norm x).val+(boundaryRePowerRow77_22Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree63Norm x).property (boundaryRePowerRow77_22Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree63Norm,boundaryRePowerRow77_22Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))=(boundaryRePowerRow77_20Degree63Norm x).val+(boundaryFullPowerDegree63Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree63Norm x).property (boundaryFullPowerDegree63Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree63Norm,boundaryFullPowerDegree63Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))))=(boundaryFullPowerDegree63Block16Norm x).val+(boundaryFullPowerDegree63Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block16Norm x).property (boundaryFullPowerDegree63Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block16Norm,boundaryFullPowerDegree63Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))))))=(boundaryFullPowerDegree63Block14Norm x).val+(boundaryFullPowerDegree63Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block14Norm x).property (boundaryFullPowerDegree63Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block14Norm,boundaryFullPowerDegree63Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x)))))))))+(((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x)))))))))+(((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x))))))))))=(boundaryFullPowerDegree63Block9Norm x).val+(boundaryFullPowerDegree63Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block9Norm x).property (boundaryFullPowerDegree63Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block9Norm,boundaryFullPowerDegree63Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x))=c} := by

  have he : ((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x))=(boundaryImPowerRow77_0Degree63Norm x).val+(boundaryImPowerRow77_1Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree63Norm x).property (boundaryImPowerRow77_1Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree63Norm,boundaryImPowerRow77_1Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x))=c} := by

  have he : ((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x))=(boundaryImPowerRow77_3Degree63Norm x).val+(boundaryImPowerRow77_4Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree63Norm x).property (boundaryImPowerRow77_4Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree63Norm,boundaryImPowerRow77_4Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x))))=(boundaryImPowerRow77_2Degree63Norm x).val+(boundaryFullPowerDegree63Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree63Norm x).property (boundaryFullPowerDegree63Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree63Norm,boundaryFullPowerDegree63Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x))))))=(boundaryFullPowerDegree63Block22Norm x).val+(boundaryFullPowerDegree63Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block22Norm x).property (boundaryFullPowerDegree63Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block22Norm,boundaryFullPowerDegree63Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x))=c} := by

  have he : ((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x))=(boundaryImPowerRow77_6Degree63Norm x).val+(boundaryImPowerRow77_7Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree63Norm x).property (boundaryImPowerRow77_7Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree63Norm,boundaryImPowerRow77_7Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x))))=(boundaryImPowerRow77_5Degree63Norm x).val+(boundaryFullPowerDegree63Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree63Norm x).property (boundaryFullPowerDegree63Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree63Norm,boundaryFullPowerDegree63Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))=c} := by

  have he : ((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))=(boundaryImPowerRow77_9Degree63Norm x).val+(boundaryImPowerRow77_10Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree63Norm x).property (boundaryImPowerRow77_10Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree63Norm,boundaryImPowerRow77_10Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))))=(boundaryImPowerRow77_8Degree63Norm x).val+(boundaryFullPowerDegree63Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree63Norm x).property (boundaryFullPowerDegree63Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree63Norm,boundaryFullPowerDegree63Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))))))=(boundaryFullPowerDegree63Block27Norm x).val+(boundaryFullPowerDegree63Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block27Norm x).property (boundaryFullPowerDegree63Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block27Norm,boundaryFullPowerDegree63Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x))))))))=(boundaryFullPowerDegree63Block25Norm x).val+(boundaryFullPowerDegree63Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block25Norm x).property (boundaryFullPowerDegree63Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block25Norm,boundaryFullPowerDegree63Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x))=c} := by

  have he : ((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x))=(boundaryImPowerRow77_12Degree63Norm x).val+(boundaryImPowerRow77_13Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree63Norm x).property (boundaryImPowerRow77_13Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree63Norm,boundaryImPowerRow77_13Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x))))=(boundaryImPowerRow77_11Degree63Norm x).val+(boundaryFullPowerDegree63Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree63Norm x).property (boundaryFullPowerDegree63Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree63Norm,boundaryFullPowerDegree63Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x))=c} := by

  have he : ((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x))=(boundaryImPowerRow77_15Degree63Norm x).val+(boundaryImPowerRow77_16Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree63Norm x).property (boundaryImPowerRow77_16Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree63Norm,boundaryImPowerRow77_16Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x))))=(boundaryImPowerRow77_14Degree63Norm x).val+(boundaryFullPowerDegree63Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree63Norm x).property (boundaryFullPowerDegree63Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree63Norm,boundaryFullPowerDegree63Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x))))))=(boundaryFullPowerDegree63Block33Norm x).val+(boundaryFullPowerDegree63Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block33Norm x).property (boundaryFullPowerDegree63Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block33Norm,boundaryFullPowerDegree63Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x))=c} := by

  have he : ((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x))=(boundaryImPowerRow77_18Degree63Norm x).val+(boundaryImPowerRow77_19Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree63Norm x).property (boundaryImPowerRow77_19Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree63Norm,boundaryImPowerRow77_19Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x))))=(boundaryImPowerRow77_17Degree63Norm x).val+(boundaryFullPowerDegree63Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree63Norm x).property (boundaryFullPowerDegree63Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree63Norm,boundaryFullPowerDegree63Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))=c} := by

  have he : ((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))=(boundaryImPowerRow77_21Degree63Norm x).val+(boundaryLowPowerRow77Degree63Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree63Norm x).property (boundaryLowPowerRow77Degree63Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree63Norm,boundaryLowPowerRow77Degree63Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))=(boundaryImPowerRow77_20Degree63Norm x).val+(boundaryFullPowerDegree63Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree63Norm x).property (boundaryFullPowerDegree63Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree63Norm,boundaryFullPowerDegree63Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))=(boundaryFullPowerDegree63Block38Norm x).val+(boundaryFullPowerDegree63Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block38Norm x).property (boundaryFullPowerDegree63Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block38Norm,boundaryFullPowerDegree63Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))))=(boundaryFullPowerDegree63Block36Norm x).val+(boundaryFullPowerDegree63Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block36Norm x).property (boundaryFullPowerDegree63Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block36Norm,boundaryFullPowerDegree63Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x)))))))))+(((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x)))))))))+(((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))))))=(boundaryFullPowerDegree63Block31Norm x).val+(boundaryFullPowerDegree63Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block31Norm x).property (boundaryFullPowerDegree63Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block31Norm,boundaryFullPowerDegree63Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree63Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x)))))))))+(((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x)))))))))))+(((((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x)))))))))+(((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x)))))))))+(((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x)))))))))))+(((((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x)))))))))+(((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x))))))))))))=(boundaryFullPowerDegree63Block21Norm x).val+(boundaryFullPowerDegree63Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree63Block21Norm x).property (boundaryFullPowerDegree63Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block21Norm,boundaryFullPowerDegree63Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree63Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 63 x=c} := by

  have he0 : boundaryFullPowerRow77 63 x=((((((((((boundaryRePowerRow77_0 63 x)+(boundaryRePowerRow77_1 63 x)))+(((boundaryRePowerRow77_2 63 x)+(((boundaryRePowerRow77_3 63 x)+(boundaryRePowerRow77_4 63 x)))))))+(((((boundaryRePowerRow77_5 63 x)+(((boundaryRePowerRow77_6 63 x)+(boundaryRePowerRow77_7 63 x)))))+(((boundaryRePowerRow77_8 63 x)+(((boundaryRePowerRow77_9 63 x)+(boundaryRePowerRow77_10 63 x)))))))))+(((((((boundaryRePowerRow77_11 63 x)+(((boundaryRePowerRow77_12 63 x)+(boundaryRePowerRow77_13 63 x)))))+(((boundaryRePowerRow77_14 63 x)+(((boundaryRePowerRow77_15 63 x)+(boundaryRePowerRow77_16 63 x)))))))+(((((boundaryRePowerRow77_17 63 x)+(((boundaryRePowerRow77_18 63 x)+(boundaryRePowerRow77_19 63 x)))))+(((boundaryRePowerRow77_20 63 x)+(((boundaryRePowerRow77_21 63 x)+(boundaryRePowerRow77_22 63 x)))))))))))+(((((((((boundaryImPowerRow77_0 63 x)+(boundaryImPowerRow77_1 63 x)))+(((boundaryImPowerRow77_2 63 x)+(((boundaryImPowerRow77_3 63 x)+(boundaryImPowerRow77_4 63 x)))))))+(((((boundaryImPowerRow77_5 63 x)+(((boundaryImPowerRow77_6 63 x)+(boundaryImPowerRow77_7 63 x)))))+(((boundaryImPowerRow77_8 63 x)+(((boundaryImPowerRow77_9 63 x)+(boundaryImPowerRow77_10 63 x)))))))))+(((((((boundaryImPowerRow77_11 63 x)+(((boundaryImPowerRow77_12 63 x)+(boundaryImPowerRow77_13 63 x)))))+(((boundaryImPowerRow77_14 63 x)+(((boundaryImPowerRow77_15 63 x)+(boundaryImPowerRow77_16 63 x)))))))+(((((boundaryImPowerRow77_17 63 x)+(((boundaryImPowerRow77_18 63 x)+(boundaryImPowerRow77_19 63 x)))))+(((boundaryImPowerRow77_20 63 x)+(((boundaryImPowerRow77_21 63 x)+(boundaryLowPowerRow77 63 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree63Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree63Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
