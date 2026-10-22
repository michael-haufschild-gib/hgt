import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree20Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree20Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x))=c} := by

  have he : ((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x))=(boundaryRePowerRow77_0Degree20Norm x).val+(boundaryRePowerRow77_1Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree20Norm x).property (boundaryRePowerRow77_1Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree20Norm,boundaryRePowerRow77_1Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x))=c} := by

  have he : ((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x))=(boundaryRePowerRow77_3Degree20Norm x).val+(boundaryRePowerRow77_4Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree20Norm x).property (boundaryRePowerRow77_4Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree20Norm,boundaryRePowerRow77_4Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x))))=(boundaryRePowerRow77_2Degree20Norm x).val+(boundaryFullPowerDegree20Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree20Norm x).property (boundaryFullPowerDegree20Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree20Norm,boundaryFullPowerDegree20Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x))))))=(boundaryFullPowerDegree20Block0Norm x).val+(boundaryFullPowerDegree20Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block0Norm x).property (boundaryFullPowerDegree20Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block0Norm,boundaryFullPowerDegree20Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x))=c} := by

  have he : ((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x))=(boundaryRePowerRow77_6Degree20Norm x).val+(boundaryRePowerRow77_7Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree20Norm x).property (boundaryRePowerRow77_7Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree20Norm,boundaryRePowerRow77_7Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x))))=(boundaryRePowerRow77_5Degree20Norm x).val+(boundaryFullPowerDegree20Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree20Norm x).property (boundaryFullPowerDegree20Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree20Norm,boundaryFullPowerDegree20Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))=c} := by

  have he : ((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))=(boundaryRePowerRow77_9Degree20Norm x).val+(boundaryRePowerRow77_10Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree20Norm x).property (boundaryRePowerRow77_10Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree20Norm,boundaryRePowerRow77_10Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))))=(boundaryRePowerRow77_8Degree20Norm x).val+(boundaryFullPowerDegree20Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree20Norm x).property (boundaryFullPowerDegree20Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree20Norm,boundaryFullPowerDegree20Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))))))=(boundaryFullPowerDegree20Block5Norm x).val+(boundaryFullPowerDegree20Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block5Norm x).property (boundaryFullPowerDegree20Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block5Norm,boundaryFullPowerDegree20Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x))))))))=(boundaryFullPowerDegree20Block3Norm x).val+(boundaryFullPowerDegree20Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block3Norm x).property (boundaryFullPowerDegree20Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block3Norm,boundaryFullPowerDegree20Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x))=c} := by

  have he : ((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x))=(boundaryRePowerRow77_12Degree20Norm x).val+(boundaryRePowerRow77_13Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree20Norm x).property (boundaryRePowerRow77_13Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree20Norm,boundaryRePowerRow77_13Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x))))=(boundaryRePowerRow77_11Degree20Norm x).val+(boundaryFullPowerDegree20Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree20Norm x).property (boundaryFullPowerDegree20Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree20Norm,boundaryFullPowerDegree20Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x))=c} := by

  have he : ((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x))=(boundaryRePowerRow77_15Degree20Norm x).val+(boundaryRePowerRow77_16Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree20Norm x).property (boundaryRePowerRow77_16Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree20Norm,boundaryRePowerRow77_16Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x))))=(boundaryRePowerRow77_14Degree20Norm x).val+(boundaryFullPowerDegree20Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree20Norm x).property (boundaryFullPowerDegree20Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree20Norm,boundaryFullPowerDegree20Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x))))))=(boundaryFullPowerDegree20Block11Norm x).val+(boundaryFullPowerDegree20Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block11Norm x).property (boundaryFullPowerDegree20Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block11Norm,boundaryFullPowerDegree20Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x))=c} := by

  have he : ((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x))=(boundaryRePowerRow77_18Degree20Norm x).val+(boundaryRePowerRow77_19Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree20Norm x).property (boundaryRePowerRow77_19Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree20Norm,boundaryRePowerRow77_19Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x))))=(boundaryRePowerRow77_17Degree20Norm x).val+(boundaryFullPowerDegree20Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree20Norm x).property (boundaryFullPowerDegree20Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree20Norm,boundaryFullPowerDegree20Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))=c} := by

  have he : ((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))=(boundaryRePowerRow77_21Degree20Norm x).val+(boundaryRePowerRow77_22Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree20Norm x).property (boundaryRePowerRow77_22Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree20Norm,boundaryRePowerRow77_22Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))=(boundaryRePowerRow77_20Degree20Norm x).val+(boundaryFullPowerDegree20Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree20Norm x).property (boundaryFullPowerDegree20Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree20Norm,boundaryFullPowerDegree20Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))))=(boundaryFullPowerDegree20Block16Norm x).val+(boundaryFullPowerDegree20Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block16Norm x).property (boundaryFullPowerDegree20Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block16Norm,boundaryFullPowerDegree20Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))))))=(boundaryFullPowerDegree20Block14Norm x).val+(boundaryFullPowerDegree20Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block14Norm x).property (boundaryFullPowerDegree20Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block14Norm,boundaryFullPowerDegree20Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x)))))))))+(((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x)))))))))+(((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x))))))))))=(boundaryFullPowerDegree20Block9Norm x).val+(boundaryFullPowerDegree20Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block9Norm x).property (boundaryFullPowerDegree20Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block9Norm,boundaryFullPowerDegree20Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x))=c} := by

  have he : ((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x))=(boundaryImPowerRow77_0Degree20Norm x).val+(boundaryImPowerRow77_1Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree20Norm x).property (boundaryImPowerRow77_1Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree20Norm,boundaryImPowerRow77_1Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x))=c} := by

  have he : ((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x))=(boundaryImPowerRow77_3Degree20Norm x).val+(boundaryImPowerRow77_4Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree20Norm x).property (boundaryImPowerRow77_4Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree20Norm,boundaryImPowerRow77_4Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x))))=(boundaryImPowerRow77_2Degree20Norm x).val+(boundaryFullPowerDegree20Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree20Norm x).property (boundaryFullPowerDegree20Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree20Norm,boundaryFullPowerDegree20Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x))))))=(boundaryFullPowerDegree20Block22Norm x).val+(boundaryFullPowerDegree20Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block22Norm x).property (boundaryFullPowerDegree20Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block22Norm,boundaryFullPowerDegree20Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x))=c} := by

  have he : ((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x))=(boundaryImPowerRow77_6Degree20Norm x).val+(boundaryImPowerRow77_7Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree20Norm x).property (boundaryImPowerRow77_7Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree20Norm,boundaryImPowerRow77_7Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x))))=(boundaryImPowerRow77_5Degree20Norm x).val+(boundaryFullPowerDegree20Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree20Norm x).property (boundaryFullPowerDegree20Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree20Norm,boundaryFullPowerDegree20Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))=c} := by

  have he : ((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))=(boundaryImPowerRow77_9Degree20Norm x).val+(boundaryImPowerRow77_10Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree20Norm x).property (boundaryImPowerRow77_10Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree20Norm,boundaryImPowerRow77_10Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))))=(boundaryImPowerRow77_8Degree20Norm x).val+(boundaryFullPowerDegree20Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree20Norm x).property (boundaryFullPowerDegree20Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree20Norm,boundaryFullPowerDegree20Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))))))=(boundaryFullPowerDegree20Block27Norm x).val+(boundaryFullPowerDegree20Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block27Norm x).property (boundaryFullPowerDegree20Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block27Norm,boundaryFullPowerDegree20Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x))))))))=(boundaryFullPowerDegree20Block25Norm x).val+(boundaryFullPowerDegree20Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block25Norm x).property (boundaryFullPowerDegree20Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block25Norm,boundaryFullPowerDegree20Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x))=c} := by

  have he : ((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x))=(boundaryImPowerRow77_12Degree20Norm x).val+(boundaryImPowerRow77_13Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree20Norm x).property (boundaryImPowerRow77_13Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree20Norm,boundaryImPowerRow77_13Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x))))=(boundaryImPowerRow77_11Degree20Norm x).val+(boundaryFullPowerDegree20Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree20Norm x).property (boundaryFullPowerDegree20Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree20Norm,boundaryFullPowerDegree20Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x))=c} := by

  have he : ((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x))=(boundaryImPowerRow77_15Degree20Norm x).val+(boundaryImPowerRow77_16Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree20Norm x).property (boundaryImPowerRow77_16Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree20Norm,boundaryImPowerRow77_16Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x))))=(boundaryImPowerRow77_14Degree20Norm x).val+(boundaryFullPowerDegree20Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree20Norm x).property (boundaryFullPowerDegree20Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree20Norm,boundaryFullPowerDegree20Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x))))))=(boundaryFullPowerDegree20Block33Norm x).val+(boundaryFullPowerDegree20Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block33Norm x).property (boundaryFullPowerDegree20Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block33Norm,boundaryFullPowerDegree20Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x))=c} := by

  have he : ((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x))=(boundaryImPowerRow77_18Degree20Norm x).val+(boundaryImPowerRow77_19Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree20Norm x).property (boundaryImPowerRow77_19Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree20Norm,boundaryImPowerRow77_19Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x))))=(boundaryImPowerRow77_17Degree20Norm x).val+(boundaryFullPowerDegree20Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree20Norm x).property (boundaryFullPowerDegree20Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree20Norm,boundaryFullPowerDegree20Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))=c} := by

  have he : ((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))=(boundaryImPowerRow77_21Degree20Norm x).val+(boundaryLowPowerRow77Degree20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree20Norm x).property (boundaryLowPowerRow77Degree20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree20Norm,boundaryLowPowerRow77Degree20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))=(boundaryImPowerRow77_20Degree20Norm x).val+(boundaryFullPowerDegree20Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree20Norm x).property (boundaryFullPowerDegree20Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree20Norm,boundaryFullPowerDegree20Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))=(boundaryFullPowerDegree20Block38Norm x).val+(boundaryFullPowerDegree20Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block38Norm x).property (boundaryFullPowerDegree20Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block38Norm,boundaryFullPowerDegree20Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))))=(boundaryFullPowerDegree20Block36Norm x).val+(boundaryFullPowerDegree20Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block36Norm x).property (boundaryFullPowerDegree20Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block36Norm,boundaryFullPowerDegree20Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x)))))))))+(((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x)))))))))+(((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))))))=(boundaryFullPowerDegree20Block31Norm x).val+(boundaryFullPowerDegree20Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block31Norm x).property (boundaryFullPowerDegree20Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block31Norm,boundaryFullPowerDegree20Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree20Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x)))))))))+(((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x)))))))))))+(((((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x)))))))))+(((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x)))))))))+(((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x)))))))))))+(((((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x)))))))))+(((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x))))))))))))=(boundaryFullPowerDegree20Block21Norm x).val+(boundaryFullPowerDegree20Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree20Block21Norm x).property (boundaryFullPowerDegree20Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block21Norm,boundaryFullPowerDegree20Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree20Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 20 x=c} := by

  have he0 : boundaryFullPowerRow77 20 x=((((((((((boundaryRePowerRow77_0 20 x)+(boundaryRePowerRow77_1 20 x)))+(((boundaryRePowerRow77_2 20 x)+(((boundaryRePowerRow77_3 20 x)+(boundaryRePowerRow77_4 20 x)))))))+(((((boundaryRePowerRow77_5 20 x)+(((boundaryRePowerRow77_6 20 x)+(boundaryRePowerRow77_7 20 x)))))+(((boundaryRePowerRow77_8 20 x)+(((boundaryRePowerRow77_9 20 x)+(boundaryRePowerRow77_10 20 x)))))))))+(((((((boundaryRePowerRow77_11 20 x)+(((boundaryRePowerRow77_12 20 x)+(boundaryRePowerRow77_13 20 x)))))+(((boundaryRePowerRow77_14 20 x)+(((boundaryRePowerRow77_15 20 x)+(boundaryRePowerRow77_16 20 x)))))))+(((((boundaryRePowerRow77_17 20 x)+(((boundaryRePowerRow77_18 20 x)+(boundaryRePowerRow77_19 20 x)))))+(((boundaryRePowerRow77_20 20 x)+(((boundaryRePowerRow77_21 20 x)+(boundaryRePowerRow77_22 20 x)))))))))))+(((((((((boundaryImPowerRow77_0 20 x)+(boundaryImPowerRow77_1 20 x)))+(((boundaryImPowerRow77_2 20 x)+(((boundaryImPowerRow77_3 20 x)+(boundaryImPowerRow77_4 20 x)))))))+(((((boundaryImPowerRow77_5 20 x)+(((boundaryImPowerRow77_6 20 x)+(boundaryImPowerRow77_7 20 x)))))+(((boundaryImPowerRow77_8 20 x)+(((boundaryImPowerRow77_9 20 x)+(boundaryImPowerRow77_10 20 x)))))))))+(((((((boundaryImPowerRow77_11 20 x)+(((boundaryImPowerRow77_12 20 x)+(boundaryImPowerRow77_13 20 x)))))+(((boundaryImPowerRow77_14 20 x)+(((boundaryImPowerRow77_15 20 x)+(boundaryImPowerRow77_16 20 x)))))))+(((((boundaryImPowerRow77_17 20 x)+(((boundaryImPowerRow77_18 20 x)+(boundaryImPowerRow77_19 20 x)))))+(((boundaryImPowerRow77_20 20 x)+(((boundaryImPowerRow77_21 20 x)+(boundaryLowPowerRow77 20 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree20Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree20Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
