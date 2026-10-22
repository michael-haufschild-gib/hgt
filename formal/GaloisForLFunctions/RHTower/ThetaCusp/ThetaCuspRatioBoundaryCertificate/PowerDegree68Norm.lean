import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree68Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree68Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x))=c} := by

  have he : ((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x))=(boundaryRePowerRow77_0Degree68Norm x).val+(boundaryRePowerRow77_1Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree68Norm x).property (boundaryRePowerRow77_1Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree68Norm,boundaryRePowerRow77_1Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x))=c} := by

  have he : ((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x))=(boundaryRePowerRow77_3Degree68Norm x).val+(boundaryRePowerRow77_4Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree68Norm x).property (boundaryRePowerRow77_4Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree68Norm,boundaryRePowerRow77_4Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x))))=(boundaryRePowerRow77_2Degree68Norm x).val+(boundaryFullPowerDegree68Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree68Norm x).property (boundaryFullPowerDegree68Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree68Norm,boundaryFullPowerDegree68Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x))))))=(boundaryFullPowerDegree68Block0Norm x).val+(boundaryFullPowerDegree68Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block0Norm x).property (boundaryFullPowerDegree68Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block0Norm,boundaryFullPowerDegree68Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x))=c} := by

  have he : ((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x))=(boundaryRePowerRow77_6Degree68Norm x).val+(boundaryRePowerRow77_7Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree68Norm x).property (boundaryRePowerRow77_7Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree68Norm,boundaryRePowerRow77_7Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x))))=(boundaryRePowerRow77_5Degree68Norm x).val+(boundaryFullPowerDegree68Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree68Norm x).property (boundaryFullPowerDegree68Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree68Norm,boundaryFullPowerDegree68Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))=c} := by

  have he : ((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))=(boundaryRePowerRow77_9Degree68Norm x).val+(boundaryRePowerRow77_10Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree68Norm x).property (boundaryRePowerRow77_10Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree68Norm,boundaryRePowerRow77_10Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))))=(boundaryRePowerRow77_8Degree68Norm x).val+(boundaryFullPowerDegree68Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree68Norm x).property (boundaryFullPowerDegree68Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree68Norm,boundaryFullPowerDegree68Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))))))=(boundaryFullPowerDegree68Block5Norm x).val+(boundaryFullPowerDegree68Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block5Norm x).property (boundaryFullPowerDegree68Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block5Norm,boundaryFullPowerDegree68Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x))))))))=(boundaryFullPowerDegree68Block3Norm x).val+(boundaryFullPowerDegree68Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block3Norm x).property (boundaryFullPowerDegree68Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block3Norm,boundaryFullPowerDegree68Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x))=c} := by

  have he : ((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x))=(boundaryRePowerRow77_12Degree68Norm x).val+(boundaryRePowerRow77_13Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree68Norm x).property (boundaryRePowerRow77_13Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree68Norm,boundaryRePowerRow77_13Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x))))=(boundaryRePowerRow77_11Degree68Norm x).val+(boundaryFullPowerDegree68Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree68Norm x).property (boundaryFullPowerDegree68Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree68Norm,boundaryFullPowerDegree68Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x))=c} := by

  have he : ((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x))=(boundaryRePowerRow77_15Degree68Norm x).val+(boundaryRePowerRow77_16Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree68Norm x).property (boundaryRePowerRow77_16Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree68Norm,boundaryRePowerRow77_16Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x))))=(boundaryRePowerRow77_14Degree68Norm x).val+(boundaryFullPowerDegree68Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree68Norm x).property (boundaryFullPowerDegree68Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree68Norm,boundaryFullPowerDegree68Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x))))))=(boundaryFullPowerDegree68Block11Norm x).val+(boundaryFullPowerDegree68Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block11Norm x).property (boundaryFullPowerDegree68Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block11Norm,boundaryFullPowerDegree68Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x))=c} := by

  have he : ((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x))=(boundaryRePowerRow77_18Degree68Norm x).val+(boundaryRePowerRow77_19Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree68Norm x).property (boundaryRePowerRow77_19Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree68Norm,boundaryRePowerRow77_19Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x))))=(boundaryRePowerRow77_17Degree68Norm x).val+(boundaryFullPowerDegree68Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree68Norm x).property (boundaryFullPowerDegree68Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree68Norm,boundaryFullPowerDegree68Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))=c} := by

  have he : ((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))=(boundaryRePowerRow77_21Degree68Norm x).val+(boundaryRePowerRow77_22Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree68Norm x).property (boundaryRePowerRow77_22Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree68Norm,boundaryRePowerRow77_22Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))=(boundaryRePowerRow77_20Degree68Norm x).val+(boundaryFullPowerDegree68Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree68Norm x).property (boundaryFullPowerDegree68Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree68Norm,boundaryFullPowerDegree68Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))))=(boundaryFullPowerDegree68Block16Norm x).val+(boundaryFullPowerDegree68Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block16Norm x).property (boundaryFullPowerDegree68Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block16Norm,boundaryFullPowerDegree68Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))))))=(boundaryFullPowerDegree68Block14Norm x).val+(boundaryFullPowerDegree68Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block14Norm x).property (boundaryFullPowerDegree68Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block14Norm,boundaryFullPowerDegree68Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x)))))))))+(((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x)))))))))+(((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x))))))))))=(boundaryFullPowerDegree68Block9Norm x).val+(boundaryFullPowerDegree68Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block9Norm x).property (boundaryFullPowerDegree68Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block9Norm,boundaryFullPowerDegree68Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x))=c} := by

  have he : ((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x))=(boundaryImPowerRow77_0Degree68Norm x).val+(boundaryImPowerRow77_1Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree68Norm x).property (boundaryImPowerRow77_1Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree68Norm,boundaryImPowerRow77_1Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x))=c} := by

  have he : ((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x))=(boundaryImPowerRow77_3Degree68Norm x).val+(boundaryImPowerRow77_4Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree68Norm x).property (boundaryImPowerRow77_4Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree68Norm,boundaryImPowerRow77_4Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x))))=(boundaryImPowerRow77_2Degree68Norm x).val+(boundaryFullPowerDegree68Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree68Norm x).property (boundaryFullPowerDegree68Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree68Norm,boundaryFullPowerDegree68Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x))))))=(boundaryFullPowerDegree68Block22Norm x).val+(boundaryFullPowerDegree68Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block22Norm x).property (boundaryFullPowerDegree68Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block22Norm,boundaryFullPowerDegree68Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x))=c} := by

  have he : ((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x))=(boundaryImPowerRow77_6Degree68Norm x).val+(boundaryImPowerRow77_7Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree68Norm x).property (boundaryImPowerRow77_7Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree68Norm,boundaryImPowerRow77_7Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x))))=(boundaryImPowerRow77_5Degree68Norm x).val+(boundaryFullPowerDegree68Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree68Norm x).property (boundaryFullPowerDegree68Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree68Norm,boundaryFullPowerDegree68Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))=c} := by

  have he : ((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))=(boundaryImPowerRow77_9Degree68Norm x).val+(boundaryImPowerRow77_10Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree68Norm x).property (boundaryImPowerRow77_10Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree68Norm,boundaryImPowerRow77_10Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))))=(boundaryImPowerRow77_8Degree68Norm x).val+(boundaryFullPowerDegree68Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree68Norm x).property (boundaryFullPowerDegree68Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree68Norm,boundaryFullPowerDegree68Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))))))=(boundaryFullPowerDegree68Block27Norm x).val+(boundaryFullPowerDegree68Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block27Norm x).property (boundaryFullPowerDegree68Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block27Norm,boundaryFullPowerDegree68Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x))))))))=(boundaryFullPowerDegree68Block25Norm x).val+(boundaryFullPowerDegree68Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block25Norm x).property (boundaryFullPowerDegree68Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block25Norm,boundaryFullPowerDegree68Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x))=c} := by

  have he : ((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x))=(boundaryImPowerRow77_12Degree68Norm x).val+(boundaryImPowerRow77_13Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree68Norm x).property (boundaryImPowerRow77_13Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree68Norm,boundaryImPowerRow77_13Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x))))=(boundaryImPowerRow77_11Degree68Norm x).val+(boundaryFullPowerDegree68Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree68Norm x).property (boundaryFullPowerDegree68Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree68Norm,boundaryFullPowerDegree68Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x))=c} := by

  have he : ((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x))=(boundaryImPowerRow77_15Degree68Norm x).val+(boundaryImPowerRow77_16Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree68Norm x).property (boundaryImPowerRow77_16Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree68Norm,boundaryImPowerRow77_16Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x))))=(boundaryImPowerRow77_14Degree68Norm x).val+(boundaryFullPowerDegree68Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree68Norm x).property (boundaryFullPowerDegree68Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree68Norm,boundaryFullPowerDegree68Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x))))))=(boundaryFullPowerDegree68Block33Norm x).val+(boundaryFullPowerDegree68Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block33Norm x).property (boundaryFullPowerDegree68Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block33Norm,boundaryFullPowerDegree68Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x))=c} := by

  have he : ((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x))=(boundaryImPowerRow77_18Degree68Norm x).val+(boundaryImPowerRow77_19Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree68Norm x).property (boundaryImPowerRow77_19Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree68Norm,boundaryImPowerRow77_19Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x))))=(boundaryImPowerRow77_17Degree68Norm x).val+(boundaryFullPowerDegree68Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree68Norm x).property (boundaryFullPowerDegree68Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree68Norm,boundaryFullPowerDegree68Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))=c} := by

  have he : ((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))=(boundaryImPowerRow77_21Degree68Norm x).val+(boundaryLowPowerRow77Degree68Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree68Norm x).property (boundaryLowPowerRow77Degree68Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree68Norm,boundaryLowPowerRow77Degree68Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))=(boundaryImPowerRow77_20Degree68Norm x).val+(boundaryFullPowerDegree68Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree68Norm x).property (boundaryFullPowerDegree68Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree68Norm,boundaryFullPowerDegree68Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))=(boundaryFullPowerDegree68Block38Norm x).val+(boundaryFullPowerDegree68Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block38Norm x).property (boundaryFullPowerDegree68Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block38Norm,boundaryFullPowerDegree68Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))))=(boundaryFullPowerDegree68Block36Norm x).val+(boundaryFullPowerDegree68Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block36Norm x).property (boundaryFullPowerDegree68Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block36Norm,boundaryFullPowerDegree68Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x)))))))))+(((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x)))))))))+(((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))))))=(boundaryFullPowerDegree68Block31Norm x).val+(boundaryFullPowerDegree68Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block31Norm x).property (boundaryFullPowerDegree68Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block31Norm,boundaryFullPowerDegree68Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree68Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x)))))))))+(((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x)))))))))))+(((((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x)))))))))+(((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x)))))))))+(((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x)))))))))))+(((((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x)))))))))+(((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x))))))))))))=(boundaryFullPowerDegree68Block21Norm x).val+(boundaryFullPowerDegree68Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree68Block21Norm x).property (boundaryFullPowerDegree68Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block21Norm,boundaryFullPowerDegree68Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree68Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 68 x=c} := by

  have he0 : boundaryFullPowerRow77 68 x=((((((((((boundaryRePowerRow77_0 68 x)+(boundaryRePowerRow77_1 68 x)))+(((boundaryRePowerRow77_2 68 x)+(((boundaryRePowerRow77_3 68 x)+(boundaryRePowerRow77_4 68 x)))))))+(((((boundaryRePowerRow77_5 68 x)+(((boundaryRePowerRow77_6 68 x)+(boundaryRePowerRow77_7 68 x)))))+(((boundaryRePowerRow77_8 68 x)+(((boundaryRePowerRow77_9 68 x)+(boundaryRePowerRow77_10 68 x)))))))))+(((((((boundaryRePowerRow77_11 68 x)+(((boundaryRePowerRow77_12 68 x)+(boundaryRePowerRow77_13 68 x)))))+(((boundaryRePowerRow77_14 68 x)+(((boundaryRePowerRow77_15 68 x)+(boundaryRePowerRow77_16 68 x)))))))+(((((boundaryRePowerRow77_17 68 x)+(((boundaryRePowerRow77_18 68 x)+(boundaryRePowerRow77_19 68 x)))))+(((boundaryRePowerRow77_20 68 x)+(((boundaryRePowerRow77_21 68 x)+(boundaryRePowerRow77_22 68 x)))))))))))+(((((((((boundaryImPowerRow77_0 68 x)+(boundaryImPowerRow77_1 68 x)))+(((boundaryImPowerRow77_2 68 x)+(((boundaryImPowerRow77_3 68 x)+(boundaryImPowerRow77_4 68 x)))))))+(((((boundaryImPowerRow77_5 68 x)+(((boundaryImPowerRow77_6 68 x)+(boundaryImPowerRow77_7 68 x)))))+(((boundaryImPowerRow77_8 68 x)+(((boundaryImPowerRow77_9 68 x)+(boundaryImPowerRow77_10 68 x)))))))))+(((((((boundaryImPowerRow77_11 68 x)+(((boundaryImPowerRow77_12 68 x)+(boundaryImPowerRow77_13 68 x)))))+(((boundaryImPowerRow77_14 68 x)+(((boundaryImPowerRow77_15 68 x)+(boundaryImPowerRow77_16 68 x)))))))+(((((boundaryImPowerRow77_17 68 x)+(((boundaryImPowerRow77_18 68 x)+(boundaryImPowerRow77_19 68 x)))))+(((boundaryImPowerRow77_20 68 x)+(((boundaryImPowerRow77_21 68 x)+(boundaryLowPowerRow77 68 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree68Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree68Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
