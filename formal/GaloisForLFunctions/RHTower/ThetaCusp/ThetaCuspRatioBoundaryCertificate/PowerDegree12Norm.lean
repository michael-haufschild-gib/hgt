import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree12Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree12Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x))=c} := by

  have he : ((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x))=(boundaryRePowerRow77_0Degree12Norm x).val+(boundaryRePowerRow77_1Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree12Norm x).property (boundaryRePowerRow77_1Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree12Norm,boundaryRePowerRow77_1Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x))=c} := by

  have he : ((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x))=(boundaryRePowerRow77_3Degree12Norm x).val+(boundaryRePowerRow77_4Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree12Norm x).property (boundaryRePowerRow77_4Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree12Norm,boundaryRePowerRow77_4Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x))))=(boundaryRePowerRow77_2Degree12Norm x).val+(boundaryFullPowerDegree12Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree12Norm x).property (boundaryFullPowerDegree12Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree12Norm,boundaryFullPowerDegree12Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x))))))=(boundaryFullPowerDegree12Block0Norm x).val+(boundaryFullPowerDegree12Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block0Norm x).property (boundaryFullPowerDegree12Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block0Norm,boundaryFullPowerDegree12Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x))=c} := by

  have he : ((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x))=(boundaryRePowerRow77_6Degree12Norm x).val+(boundaryRePowerRow77_7Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree12Norm x).property (boundaryRePowerRow77_7Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree12Norm,boundaryRePowerRow77_7Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x))))=(boundaryRePowerRow77_5Degree12Norm x).val+(boundaryFullPowerDegree12Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree12Norm x).property (boundaryFullPowerDegree12Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree12Norm,boundaryFullPowerDegree12Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))=c} := by

  have he : ((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))=(boundaryRePowerRow77_9Degree12Norm x).val+(boundaryRePowerRow77_10Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree12Norm x).property (boundaryRePowerRow77_10Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree12Norm,boundaryRePowerRow77_10Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))))=(boundaryRePowerRow77_8Degree12Norm x).val+(boundaryFullPowerDegree12Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree12Norm x).property (boundaryFullPowerDegree12Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree12Norm,boundaryFullPowerDegree12Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))))))=(boundaryFullPowerDegree12Block5Norm x).val+(boundaryFullPowerDegree12Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block5Norm x).property (boundaryFullPowerDegree12Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block5Norm,boundaryFullPowerDegree12Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x))))))))=(boundaryFullPowerDegree12Block3Norm x).val+(boundaryFullPowerDegree12Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block3Norm x).property (boundaryFullPowerDegree12Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block3Norm,boundaryFullPowerDegree12Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x))=c} := by

  have he : ((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x))=(boundaryRePowerRow77_12Degree12Norm x).val+(boundaryRePowerRow77_13Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree12Norm x).property (boundaryRePowerRow77_13Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree12Norm,boundaryRePowerRow77_13Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x))))=(boundaryRePowerRow77_11Degree12Norm x).val+(boundaryFullPowerDegree12Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree12Norm x).property (boundaryFullPowerDegree12Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree12Norm,boundaryFullPowerDegree12Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x))=c} := by

  have he : ((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x))=(boundaryRePowerRow77_15Degree12Norm x).val+(boundaryRePowerRow77_16Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree12Norm x).property (boundaryRePowerRow77_16Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree12Norm,boundaryRePowerRow77_16Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x))))=(boundaryRePowerRow77_14Degree12Norm x).val+(boundaryFullPowerDegree12Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree12Norm x).property (boundaryFullPowerDegree12Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree12Norm,boundaryFullPowerDegree12Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x))))))=(boundaryFullPowerDegree12Block11Norm x).val+(boundaryFullPowerDegree12Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block11Norm x).property (boundaryFullPowerDegree12Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block11Norm,boundaryFullPowerDegree12Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x))=c} := by

  have he : ((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x))=(boundaryRePowerRow77_18Degree12Norm x).val+(boundaryRePowerRow77_19Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree12Norm x).property (boundaryRePowerRow77_19Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree12Norm,boundaryRePowerRow77_19Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x))))=(boundaryRePowerRow77_17Degree12Norm x).val+(boundaryFullPowerDegree12Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree12Norm x).property (boundaryFullPowerDegree12Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree12Norm,boundaryFullPowerDegree12Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))=c} := by

  have he : ((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))=(boundaryRePowerRow77_21Degree12Norm x).val+(boundaryRePowerRow77_22Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree12Norm x).property (boundaryRePowerRow77_22Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree12Norm,boundaryRePowerRow77_22Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))=(boundaryRePowerRow77_20Degree12Norm x).val+(boundaryFullPowerDegree12Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree12Norm x).property (boundaryFullPowerDegree12Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree12Norm,boundaryFullPowerDegree12Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))))=(boundaryFullPowerDegree12Block16Norm x).val+(boundaryFullPowerDegree12Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block16Norm x).property (boundaryFullPowerDegree12Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block16Norm,boundaryFullPowerDegree12Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))))))=(boundaryFullPowerDegree12Block14Norm x).val+(boundaryFullPowerDegree12Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block14Norm x).property (boundaryFullPowerDegree12Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block14Norm,boundaryFullPowerDegree12Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x)))))))))+(((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x)))))))))+(((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x))))))))))=(boundaryFullPowerDegree12Block9Norm x).val+(boundaryFullPowerDegree12Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block9Norm x).property (boundaryFullPowerDegree12Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block9Norm,boundaryFullPowerDegree12Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x))=c} := by

  have he : ((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x))=(boundaryImPowerRow77_0Degree12Norm x).val+(boundaryImPowerRow77_1Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree12Norm x).property (boundaryImPowerRow77_1Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree12Norm,boundaryImPowerRow77_1Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x))=c} := by

  have he : ((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x))=(boundaryImPowerRow77_3Degree12Norm x).val+(boundaryImPowerRow77_4Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree12Norm x).property (boundaryImPowerRow77_4Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree12Norm,boundaryImPowerRow77_4Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x))))=(boundaryImPowerRow77_2Degree12Norm x).val+(boundaryFullPowerDegree12Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree12Norm x).property (boundaryFullPowerDegree12Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree12Norm,boundaryFullPowerDegree12Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x))))))=(boundaryFullPowerDegree12Block22Norm x).val+(boundaryFullPowerDegree12Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block22Norm x).property (boundaryFullPowerDegree12Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block22Norm,boundaryFullPowerDegree12Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x))=c} := by

  have he : ((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x))=(boundaryImPowerRow77_6Degree12Norm x).val+(boundaryImPowerRow77_7Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree12Norm x).property (boundaryImPowerRow77_7Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree12Norm,boundaryImPowerRow77_7Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x))))=(boundaryImPowerRow77_5Degree12Norm x).val+(boundaryFullPowerDegree12Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree12Norm x).property (boundaryFullPowerDegree12Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree12Norm,boundaryFullPowerDegree12Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))=c} := by

  have he : ((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))=(boundaryImPowerRow77_9Degree12Norm x).val+(boundaryImPowerRow77_10Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree12Norm x).property (boundaryImPowerRow77_10Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree12Norm,boundaryImPowerRow77_10Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))))=(boundaryImPowerRow77_8Degree12Norm x).val+(boundaryFullPowerDegree12Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree12Norm x).property (boundaryFullPowerDegree12Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree12Norm,boundaryFullPowerDegree12Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))))))=(boundaryFullPowerDegree12Block27Norm x).val+(boundaryFullPowerDegree12Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block27Norm x).property (boundaryFullPowerDegree12Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block27Norm,boundaryFullPowerDegree12Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x))))))))=(boundaryFullPowerDegree12Block25Norm x).val+(boundaryFullPowerDegree12Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block25Norm x).property (boundaryFullPowerDegree12Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block25Norm,boundaryFullPowerDegree12Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x))=c} := by

  have he : ((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x))=(boundaryImPowerRow77_12Degree12Norm x).val+(boundaryImPowerRow77_13Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree12Norm x).property (boundaryImPowerRow77_13Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree12Norm,boundaryImPowerRow77_13Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x))))=(boundaryImPowerRow77_11Degree12Norm x).val+(boundaryFullPowerDegree12Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree12Norm x).property (boundaryFullPowerDegree12Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree12Norm,boundaryFullPowerDegree12Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x))=c} := by

  have he : ((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x))=(boundaryImPowerRow77_15Degree12Norm x).val+(boundaryImPowerRow77_16Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree12Norm x).property (boundaryImPowerRow77_16Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree12Norm,boundaryImPowerRow77_16Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x))))=(boundaryImPowerRow77_14Degree12Norm x).val+(boundaryFullPowerDegree12Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree12Norm x).property (boundaryFullPowerDegree12Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree12Norm,boundaryFullPowerDegree12Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x))))))=(boundaryFullPowerDegree12Block33Norm x).val+(boundaryFullPowerDegree12Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block33Norm x).property (boundaryFullPowerDegree12Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block33Norm,boundaryFullPowerDegree12Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x))=c} := by

  have he : ((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x))=(boundaryImPowerRow77_18Degree12Norm x).val+(boundaryImPowerRow77_19Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree12Norm x).property (boundaryImPowerRow77_19Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree12Norm,boundaryImPowerRow77_19Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x))))=(boundaryImPowerRow77_17Degree12Norm x).val+(boundaryFullPowerDegree12Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree12Norm x).property (boundaryFullPowerDegree12Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree12Norm,boundaryFullPowerDegree12Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))=c} := by

  have he : ((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))=(boundaryImPowerRow77_21Degree12Norm x).val+(boundaryLowPowerRow77Degree12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree12Norm x).property (boundaryLowPowerRow77Degree12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree12Norm,boundaryLowPowerRow77Degree12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))=(boundaryImPowerRow77_20Degree12Norm x).val+(boundaryFullPowerDegree12Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree12Norm x).property (boundaryFullPowerDegree12Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree12Norm,boundaryFullPowerDegree12Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))=(boundaryFullPowerDegree12Block38Norm x).val+(boundaryFullPowerDegree12Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block38Norm x).property (boundaryFullPowerDegree12Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block38Norm,boundaryFullPowerDegree12Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))))=(boundaryFullPowerDegree12Block36Norm x).val+(boundaryFullPowerDegree12Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block36Norm x).property (boundaryFullPowerDegree12Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block36Norm,boundaryFullPowerDegree12Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x)))))))))+(((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x)))))))))+(((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))))))=(boundaryFullPowerDegree12Block31Norm x).val+(boundaryFullPowerDegree12Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block31Norm x).property (boundaryFullPowerDegree12Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block31Norm,boundaryFullPowerDegree12Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree12Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x)))))))))+(((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x)))))))))))+(((((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x)))))))))+(((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x)))))))))+(((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x)))))))))))+(((((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x)))))))))+(((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x))))))))))))=(boundaryFullPowerDegree12Block21Norm x).val+(boundaryFullPowerDegree12Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree12Block21Norm x).property (boundaryFullPowerDegree12Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block21Norm,boundaryFullPowerDegree12Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree12Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 12 x=c} := by

  have he0 : boundaryFullPowerRow77 12 x=((((((((((boundaryRePowerRow77_0 12 x)+(boundaryRePowerRow77_1 12 x)))+(((boundaryRePowerRow77_2 12 x)+(((boundaryRePowerRow77_3 12 x)+(boundaryRePowerRow77_4 12 x)))))))+(((((boundaryRePowerRow77_5 12 x)+(((boundaryRePowerRow77_6 12 x)+(boundaryRePowerRow77_7 12 x)))))+(((boundaryRePowerRow77_8 12 x)+(((boundaryRePowerRow77_9 12 x)+(boundaryRePowerRow77_10 12 x)))))))))+(((((((boundaryRePowerRow77_11 12 x)+(((boundaryRePowerRow77_12 12 x)+(boundaryRePowerRow77_13 12 x)))))+(((boundaryRePowerRow77_14 12 x)+(((boundaryRePowerRow77_15 12 x)+(boundaryRePowerRow77_16 12 x)))))))+(((((boundaryRePowerRow77_17 12 x)+(((boundaryRePowerRow77_18 12 x)+(boundaryRePowerRow77_19 12 x)))))+(((boundaryRePowerRow77_20 12 x)+(((boundaryRePowerRow77_21 12 x)+(boundaryRePowerRow77_22 12 x)))))))))))+(((((((((boundaryImPowerRow77_0 12 x)+(boundaryImPowerRow77_1 12 x)))+(((boundaryImPowerRow77_2 12 x)+(((boundaryImPowerRow77_3 12 x)+(boundaryImPowerRow77_4 12 x)))))))+(((((boundaryImPowerRow77_5 12 x)+(((boundaryImPowerRow77_6 12 x)+(boundaryImPowerRow77_7 12 x)))))+(((boundaryImPowerRow77_8 12 x)+(((boundaryImPowerRow77_9 12 x)+(boundaryImPowerRow77_10 12 x)))))))))+(((((((boundaryImPowerRow77_11 12 x)+(((boundaryImPowerRow77_12 12 x)+(boundaryImPowerRow77_13 12 x)))))+(((boundaryImPowerRow77_14 12 x)+(((boundaryImPowerRow77_15 12 x)+(boundaryImPowerRow77_16 12 x)))))))+(((((boundaryImPowerRow77_17 12 x)+(((boundaryImPowerRow77_18 12 x)+(boundaryImPowerRow77_19 12 x)))))+(((boundaryImPowerRow77_20 12 x)+(((boundaryImPowerRow77_21 12 x)+(boundaryLowPowerRow77 12 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree12Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree12Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
