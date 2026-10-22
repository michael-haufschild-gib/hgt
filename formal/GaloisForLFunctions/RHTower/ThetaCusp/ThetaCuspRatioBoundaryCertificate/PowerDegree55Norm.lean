import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree55Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree55Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x))=c} := by

  have he : ((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x))=(boundaryRePowerRow77_0Degree55Norm x).val+(boundaryRePowerRow77_1Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree55Norm x).property (boundaryRePowerRow77_1Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree55Norm,boundaryRePowerRow77_1Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x))=c} := by

  have he : ((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x))=(boundaryRePowerRow77_3Degree55Norm x).val+(boundaryRePowerRow77_4Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree55Norm x).property (boundaryRePowerRow77_4Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree55Norm,boundaryRePowerRow77_4Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x))))=(boundaryRePowerRow77_2Degree55Norm x).val+(boundaryFullPowerDegree55Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree55Norm x).property (boundaryFullPowerDegree55Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree55Norm,boundaryFullPowerDegree55Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x))))))=(boundaryFullPowerDegree55Block0Norm x).val+(boundaryFullPowerDegree55Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block0Norm x).property (boundaryFullPowerDegree55Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block0Norm,boundaryFullPowerDegree55Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x))=c} := by

  have he : ((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x))=(boundaryRePowerRow77_6Degree55Norm x).val+(boundaryRePowerRow77_7Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree55Norm x).property (boundaryRePowerRow77_7Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree55Norm,boundaryRePowerRow77_7Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x))))=(boundaryRePowerRow77_5Degree55Norm x).val+(boundaryFullPowerDegree55Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree55Norm x).property (boundaryFullPowerDegree55Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree55Norm,boundaryFullPowerDegree55Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))=c} := by

  have he : ((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))=(boundaryRePowerRow77_9Degree55Norm x).val+(boundaryRePowerRow77_10Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree55Norm x).property (boundaryRePowerRow77_10Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree55Norm,boundaryRePowerRow77_10Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))))=(boundaryRePowerRow77_8Degree55Norm x).val+(boundaryFullPowerDegree55Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree55Norm x).property (boundaryFullPowerDegree55Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree55Norm,boundaryFullPowerDegree55Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))))))=(boundaryFullPowerDegree55Block5Norm x).val+(boundaryFullPowerDegree55Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block5Norm x).property (boundaryFullPowerDegree55Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block5Norm,boundaryFullPowerDegree55Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x))))))))=(boundaryFullPowerDegree55Block3Norm x).val+(boundaryFullPowerDegree55Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block3Norm x).property (boundaryFullPowerDegree55Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block3Norm,boundaryFullPowerDegree55Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x))=c} := by

  have he : ((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x))=(boundaryRePowerRow77_12Degree55Norm x).val+(boundaryRePowerRow77_13Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree55Norm x).property (boundaryRePowerRow77_13Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree55Norm,boundaryRePowerRow77_13Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x))))=(boundaryRePowerRow77_11Degree55Norm x).val+(boundaryFullPowerDegree55Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree55Norm x).property (boundaryFullPowerDegree55Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree55Norm,boundaryFullPowerDegree55Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x))=c} := by

  have he : ((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x))=(boundaryRePowerRow77_15Degree55Norm x).val+(boundaryRePowerRow77_16Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree55Norm x).property (boundaryRePowerRow77_16Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree55Norm,boundaryRePowerRow77_16Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x))))=(boundaryRePowerRow77_14Degree55Norm x).val+(boundaryFullPowerDegree55Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree55Norm x).property (boundaryFullPowerDegree55Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree55Norm,boundaryFullPowerDegree55Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x))))))=(boundaryFullPowerDegree55Block11Norm x).val+(boundaryFullPowerDegree55Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block11Norm x).property (boundaryFullPowerDegree55Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block11Norm,boundaryFullPowerDegree55Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x))=c} := by

  have he : ((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x))=(boundaryRePowerRow77_18Degree55Norm x).val+(boundaryRePowerRow77_19Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree55Norm x).property (boundaryRePowerRow77_19Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree55Norm,boundaryRePowerRow77_19Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x))))=(boundaryRePowerRow77_17Degree55Norm x).val+(boundaryFullPowerDegree55Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree55Norm x).property (boundaryFullPowerDegree55Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree55Norm,boundaryFullPowerDegree55Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))=c} := by

  have he : ((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))=(boundaryRePowerRow77_21Degree55Norm x).val+(boundaryRePowerRow77_22Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree55Norm x).property (boundaryRePowerRow77_22Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree55Norm,boundaryRePowerRow77_22Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))=(boundaryRePowerRow77_20Degree55Norm x).val+(boundaryFullPowerDegree55Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree55Norm x).property (boundaryFullPowerDegree55Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree55Norm,boundaryFullPowerDegree55Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))))=(boundaryFullPowerDegree55Block16Norm x).val+(boundaryFullPowerDegree55Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block16Norm x).property (boundaryFullPowerDegree55Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block16Norm,boundaryFullPowerDegree55Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))))))=(boundaryFullPowerDegree55Block14Norm x).val+(boundaryFullPowerDegree55Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block14Norm x).property (boundaryFullPowerDegree55Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block14Norm,boundaryFullPowerDegree55Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x)))))))))+(((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x)))))))))+(((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x))))))))))=(boundaryFullPowerDegree55Block9Norm x).val+(boundaryFullPowerDegree55Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block9Norm x).property (boundaryFullPowerDegree55Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block9Norm,boundaryFullPowerDegree55Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x))=c} := by

  have he : ((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x))=(boundaryImPowerRow77_0Degree55Norm x).val+(boundaryImPowerRow77_1Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree55Norm x).property (boundaryImPowerRow77_1Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree55Norm,boundaryImPowerRow77_1Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x))=c} := by

  have he : ((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x))=(boundaryImPowerRow77_3Degree55Norm x).val+(boundaryImPowerRow77_4Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree55Norm x).property (boundaryImPowerRow77_4Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree55Norm,boundaryImPowerRow77_4Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x))))=(boundaryImPowerRow77_2Degree55Norm x).val+(boundaryFullPowerDegree55Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree55Norm x).property (boundaryFullPowerDegree55Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree55Norm,boundaryFullPowerDegree55Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x))))))=(boundaryFullPowerDegree55Block22Norm x).val+(boundaryFullPowerDegree55Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block22Norm x).property (boundaryFullPowerDegree55Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block22Norm,boundaryFullPowerDegree55Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x))=c} := by

  have he : ((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x))=(boundaryImPowerRow77_6Degree55Norm x).val+(boundaryImPowerRow77_7Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree55Norm x).property (boundaryImPowerRow77_7Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree55Norm,boundaryImPowerRow77_7Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x))))=(boundaryImPowerRow77_5Degree55Norm x).val+(boundaryFullPowerDegree55Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree55Norm x).property (boundaryFullPowerDegree55Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree55Norm,boundaryFullPowerDegree55Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))=c} := by

  have he : ((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))=(boundaryImPowerRow77_9Degree55Norm x).val+(boundaryImPowerRow77_10Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree55Norm x).property (boundaryImPowerRow77_10Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree55Norm,boundaryImPowerRow77_10Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))))=(boundaryImPowerRow77_8Degree55Norm x).val+(boundaryFullPowerDegree55Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree55Norm x).property (boundaryFullPowerDegree55Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree55Norm,boundaryFullPowerDegree55Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))))))=(boundaryFullPowerDegree55Block27Norm x).val+(boundaryFullPowerDegree55Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block27Norm x).property (boundaryFullPowerDegree55Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block27Norm,boundaryFullPowerDegree55Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x))))))))=(boundaryFullPowerDegree55Block25Norm x).val+(boundaryFullPowerDegree55Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block25Norm x).property (boundaryFullPowerDegree55Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block25Norm,boundaryFullPowerDegree55Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x))=c} := by

  have he : ((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x))=(boundaryImPowerRow77_12Degree55Norm x).val+(boundaryImPowerRow77_13Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree55Norm x).property (boundaryImPowerRow77_13Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree55Norm,boundaryImPowerRow77_13Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x))))=(boundaryImPowerRow77_11Degree55Norm x).val+(boundaryFullPowerDegree55Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree55Norm x).property (boundaryFullPowerDegree55Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree55Norm,boundaryFullPowerDegree55Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x))=c} := by

  have he : ((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x))=(boundaryImPowerRow77_15Degree55Norm x).val+(boundaryImPowerRow77_16Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree55Norm x).property (boundaryImPowerRow77_16Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree55Norm,boundaryImPowerRow77_16Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x))))=(boundaryImPowerRow77_14Degree55Norm x).val+(boundaryFullPowerDegree55Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree55Norm x).property (boundaryFullPowerDegree55Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree55Norm,boundaryFullPowerDegree55Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x))))))=(boundaryFullPowerDegree55Block33Norm x).val+(boundaryFullPowerDegree55Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block33Norm x).property (boundaryFullPowerDegree55Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block33Norm,boundaryFullPowerDegree55Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x))=c} := by

  have he : ((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x))=(boundaryImPowerRow77_18Degree55Norm x).val+(boundaryImPowerRow77_19Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree55Norm x).property (boundaryImPowerRow77_19Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree55Norm,boundaryImPowerRow77_19Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x))))=(boundaryImPowerRow77_17Degree55Norm x).val+(boundaryFullPowerDegree55Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree55Norm x).property (boundaryFullPowerDegree55Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree55Norm,boundaryFullPowerDegree55Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))=c} := by

  have he : ((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))=(boundaryImPowerRow77_21Degree55Norm x).val+(boundaryLowPowerRow77Degree55Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree55Norm x).property (boundaryLowPowerRow77Degree55Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree55Norm,boundaryLowPowerRow77Degree55Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))=(boundaryImPowerRow77_20Degree55Norm x).val+(boundaryFullPowerDegree55Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree55Norm x).property (boundaryFullPowerDegree55Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree55Norm,boundaryFullPowerDegree55Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))=(boundaryFullPowerDegree55Block38Norm x).val+(boundaryFullPowerDegree55Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block38Norm x).property (boundaryFullPowerDegree55Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block38Norm,boundaryFullPowerDegree55Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))))=(boundaryFullPowerDegree55Block36Norm x).val+(boundaryFullPowerDegree55Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block36Norm x).property (boundaryFullPowerDegree55Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block36Norm,boundaryFullPowerDegree55Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x)))))))))+(((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x)))))))))+(((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))))))=(boundaryFullPowerDegree55Block31Norm x).val+(boundaryFullPowerDegree55Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block31Norm x).property (boundaryFullPowerDegree55Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block31Norm,boundaryFullPowerDegree55Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree55Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x)))))))))+(((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x)))))))))))+(((((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x)))))))))+(((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x)))))))))+(((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x)))))))))))+(((((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x)))))))))+(((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x))))))))))))=(boundaryFullPowerDegree55Block21Norm x).val+(boundaryFullPowerDegree55Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree55Block21Norm x).property (boundaryFullPowerDegree55Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block21Norm,boundaryFullPowerDegree55Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree55Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 55 x=c} := by

  have he0 : boundaryFullPowerRow77 55 x=((((((((((boundaryRePowerRow77_0 55 x)+(boundaryRePowerRow77_1 55 x)))+(((boundaryRePowerRow77_2 55 x)+(((boundaryRePowerRow77_3 55 x)+(boundaryRePowerRow77_4 55 x)))))))+(((((boundaryRePowerRow77_5 55 x)+(((boundaryRePowerRow77_6 55 x)+(boundaryRePowerRow77_7 55 x)))))+(((boundaryRePowerRow77_8 55 x)+(((boundaryRePowerRow77_9 55 x)+(boundaryRePowerRow77_10 55 x)))))))))+(((((((boundaryRePowerRow77_11 55 x)+(((boundaryRePowerRow77_12 55 x)+(boundaryRePowerRow77_13 55 x)))))+(((boundaryRePowerRow77_14 55 x)+(((boundaryRePowerRow77_15 55 x)+(boundaryRePowerRow77_16 55 x)))))))+(((((boundaryRePowerRow77_17 55 x)+(((boundaryRePowerRow77_18 55 x)+(boundaryRePowerRow77_19 55 x)))))+(((boundaryRePowerRow77_20 55 x)+(((boundaryRePowerRow77_21 55 x)+(boundaryRePowerRow77_22 55 x)))))))))))+(((((((((boundaryImPowerRow77_0 55 x)+(boundaryImPowerRow77_1 55 x)))+(((boundaryImPowerRow77_2 55 x)+(((boundaryImPowerRow77_3 55 x)+(boundaryImPowerRow77_4 55 x)))))))+(((((boundaryImPowerRow77_5 55 x)+(((boundaryImPowerRow77_6 55 x)+(boundaryImPowerRow77_7 55 x)))))+(((boundaryImPowerRow77_8 55 x)+(((boundaryImPowerRow77_9 55 x)+(boundaryImPowerRow77_10 55 x)))))))))+(((((((boundaryImPowerRow77_11 55 x)+(((boundaryImPowerRow77_12 55 x)+(boundaryImPowerRow77_13 55 x)))))+(((boundaryImPowerRow77_14 55 x)+(((boundaryImPowerRow77_15 55 x)+(boundaryImPowerRow77_16 55 x)))))))+(((((boundaryImPowerRow77_17 55 x)+(((boundaryImPowerRow77_18 55 x)+(boundaryImPowerRow77_19 55 x)))))+(((boundaryImPowerRow77_20 55 x)+(((boundaryImPowerRow77_21 55 x)+(boundaryLowPowerRow77 55 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree55Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree55Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
