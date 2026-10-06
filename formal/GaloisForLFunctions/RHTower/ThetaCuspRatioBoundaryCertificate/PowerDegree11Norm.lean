import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree11Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree11Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x))=c} := by

  have he : ((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x))=(boundaryRePowerRow77_0Degree11Norm x).val+(boundaryRePowerRow77_1Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree11Norm x).property (boundaryRePowerRow77_1Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree11Norm,boundaryRePowerRow77_1Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x))=c} := by

  have he : ((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x))=(boundaryRePowerRow77_3Degree11Norm x).val+(boundaryRePowerRow77_4Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree11Norm x).property (boundaryRePowerRow77_4Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree11Norm,boundaryRePowerRow77_4Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x))))=(boundaryRePowerRow77_2Degree11Norm x).val+(boundaryFullPowerDegree11Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree11Norm x).property (boundaryFullPowerDegree11Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree11Norm,boundaryFullPowerDegree11Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x))))))=(boundaryFullPowerDegree11Block0Norm x).val+(boundaryFullPowerDegree11Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block0Norm x).property (boundaryFullPowerDegree11Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block0Norm,boundaryFullPowerDegree11Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x))=c} := by

  have he : ((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x))=(boundaryRePowerRow77_6Degree11Norm x).val+(boundaryRePowerRow77_7Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree11Norm x).property (boundaryRePowerRow77_7Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree11Norm,boundaryRePowerRow77_7Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x))))=(boundaryRePowerRow77_5Degree11Norm x).val+(boundaryFullPowerDegree11Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree11Norm x).property (boundaryFullPowerDegree11Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree11Norm,boundaryFullPowerDegree11Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))=c} := by

  have he : ((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))=(boundaryRePowerRow77_9Degree11Norm x).val+(boundaryRePowerRow77_10Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree11Norm x).property (boundaryRePowerRow77_10Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree11Norm,boundaryRePowerRow77_10Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))))=(boundaryRePowerRow77_8Degree11Norm x).val+(boundaryFullPowerDegree11Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree11Norm x).property (boundaryFullPowerDegree11Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree11Norm,boundaryFullPowerDegree11Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))))))=(boundaryFullPowerDegree11Block5Norm x).val+(boundaryFullPowerDegree11Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block5Norm x).property (boundaryFullPowerDegree11Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block5Norm,boundaryFullPowerDegree11Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x))))))))=(boundaryFullPowerDegree11Block3Norm x).val+(boundaryFullPowerDegree11Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block3Norm x).property (boundaryFullPowerDegree11Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block3Norm,boundaryFullPowerDegree11Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x))=c} := by

  have he : ((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x))=(boundaryRePowerRow77_12Degree11Norm x).val+(boundaryRePowerRow77_13Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree11Norm x).property (boundaryRePowerRow77_13Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree11Norm,boundaryRePowerRow77_13Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x))))=(boundaryRePowerRow77_11Degree11Norm x).val+(boundaryFullPowerDegree11Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree11Norm x).property (boundaryFullPowerDegree11Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree11Norm,boundaryFullPowerDegree11Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x))=c} := by

  have he : ((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x))=(boundaryRePowerRow77_15Degree11Norm x).val+(boundaryRePowerRow77_16Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree11Norm x).property (boundaryRePowerRow77_16Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree11Norm,boundaryRePowerRow77_16Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x))))=(boundaryRePowerRow77_14Degree11Norm x).val+(boundaryFullPowerDegree11Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree11Norm x).property (boundaryFullPowerDegree11Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree11Norm,boundaryFullPowerDegree11Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x))))))=(boundaryFullPowerDegree11Block11Norm x).val+(boundaryFullPowerDegree11Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block11Norm x).property (boundaryFullPowerDegree11Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block11Norm,boundaryFullPowerDegree11Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x))=c} := by

  have he : ((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x))=(boundaryRePowerRow77_18Degree11Norm x).val+(boundaryRePowerRow77_19Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree11Norm x).property (boundaryRePowerRow77_19Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree11Norm,boundaryRePowerRow77_19Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x))))=(boundaryRePowerRow77_17Degree11Norm x).val+(boundaryFullPowerDegree11Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree11Norm x).property (boundaryFullPowerDegree11Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree11Norm,boundaryFullPowerDegree11Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))=c} := by

  have he : ((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))=(boundaryRePowerRow77_21Degree11Norm x).val+(boundaryRePowerRow77_22Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree11Norm x).property (boundaryRePowerRow77_22Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree11Norm,boundaryRePowerRow77_22Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))=(boundaryRePowerRow77_20Degree11Norm x).val+(boundaryFullPowerDegree11Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree11Norm x).property (boundaryFullPowerDegree11Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree11Norm,boundaryFullPowerDegree11Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))))=(boundaryFullPowerDegree11Block16Norm x).val+(boundaryFullPowerDegree11Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block16Norm x).property (boundaryFullPowerDegree11Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block16Norm,boundaryFullPowerDegree11Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))))))=(boundaryFullPowerDegree11Block14Norm x).val+(boundaryFullPowerDegree11Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block14Norm x).property (boundaryFullPowerDegree11Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block14Norm,boundaryFullPowerDegree11Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x)))))))))+(((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x)))))))))+(((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x))))))))))=(boundaryFullPowerDegree11Block9Norm x).val+(boundaryFullPowerDegree11Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block9Norm x).property (boundaryFullPowerDegree11Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block9Norm,boundaryFullPowerDegree11Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x))=c} := by

  have he : ((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x))=(boundaryImPowerRow77_0Degree11Norm x).val+(boundaryImPowerRow77_1Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree11Norm x).property (boundaryImPowerRow77_1Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree11Norm,boundaryImPowerRow77_1Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x))=c} := by

  have he : ((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x))=(boundaryImPowerRow77_3Degree11Norm x).val+(boundaryImPowerRow77_4Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree11Norm x).property (boundaryImPowerRow77_4Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree11Norm,boundaryImPowerRow77_4Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x))))=(boundaryImPowerRow77_2Degree11Norm x).val+(boundaryFullPowerDegree11Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree11Norm x).property (boundaryFullPowerDegree11Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree11Norm,boundaryFullPowerDegree11Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x))))))=(boundaryFullPowerDegree11Block22Norm x).val+(boundaryFullPowerDegree11Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block22Norm x).property (boundaryFullPowerDegree11Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block22Norm,boundaryFullPowerDegree11Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x))=c} := by

  have he : ((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x))=(boundaryImPowerRow77_6Degree11Norm x).val+(boundaryImPowerRow77_7Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree11Norm x).property (boundaryImPowerRow77_7Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree11Norm,boundaryImPowerRow77_7Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x))))=(boundaryImPowerRow77_5Degree11Norm x).val+(boundaryFullPowerDegree11Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree11Norm x).property (boundaryFullPowerDegree11Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree11Norm,boundaryFullPowerDegree11Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))=c} := by

  have he : ((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))=(boundaryImPowerRow77_9Degree11Norm x).val+(boundaryImPowerRow77_10Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree11Norm x).property (boundaryImPowerRow77_10Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree11Norm,boundaryImPowerRow77_10Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))))=(boundaryImPowerRow77_8Degree11Norm x).val+(boundaryFullPowerDegree11Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree11Norm x).property (boundaryFullPowerDegree11Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree11Norm,boundaryFullPowerDegree11Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))))))=(boundaryFullPowerDegree11Block27Norm x).val+(boundaryFullPowerDegree11Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block27Norm x).property (boundaryFullPowerDegree11Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block27Norm,boundaryFullPowerDegree11Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x))))))))=(boundaryFullPowerDegree11Block25Norm x).val+(boundaryFullPowerDegree11Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block25Norm x).property (boundaryFullPowerDegree11Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block25Norm,boundaryFullPowerDegree11Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x))=c} := by

  have he : ((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x))=(boundaryImPowerRow77_12Degree11Norm x).val+(boundaryImPowerRow77_13Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree11Norm x).property (boundaryImPowerRow77_13Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree11Norm,boundaryImPowerRow77_13Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x))))=(boundaryImPowerRow77_11Degree11Norm x).val+(boundaryFullPowerDegree11Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree11Norm x).property (boundaryFullPowerDegree11Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree11Norm,boundaryFullPowerDegree11Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x))=c} := by

  have he : ((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x))=(boundaryImPowerRow77_15Degree11Norm x).val+(boundaryImPowerRow77_16Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree11Norm x).property (boundaryImPowerRow77_16Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree11Norm,boundaryImPowerRow77_16Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x))))=(boundaryImPowerRow77_14Degree11Norm x).val+(boundaryFullPowerDegree11Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree11Norm x).property (boundaryFullPowerDegree11Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree11Norm,boundaryFullPowerDegree11Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x))))))=(boundaryFullPowerDegree11Block33Norm x).val+(boundaryFullPowerDegree11Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block33Norm x).property (boundaryFullPowerDegree11Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block33Norm,boundaryFullPowerDegree11Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x))=c} := by

  have he : ((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x))=(boundaryImPowerRow77_18Degree11Norm x).val+(boundaryImPowerRow77_19Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree11Norm x).property (boundaryImPowerRow77_19Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree11Norm,boundaryImPowerRow77_19Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x))))=(boundaryImPowerRow77_17Degree11Norm x).val+(boundaryFullPowerDegree11Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree11Norm x).property (boundaryFullPowerDegree11Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree11Norm,boundaryFullPowerDegree11Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))=c} := by

  have he : ((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))=(boundaryImPowerRow77_21Degree11Norm x).val+(boundaryLowPowerRow77Degree11Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree11Norm x).property (boundaryLowPowerRow77Degree11Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree11Norm,boundaryLowPowerRow77Degree11Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))=(boundaryImPowerRow77_20Degree11Norm x).val+(boundaryFullPowerDegree11Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree11Norm x).property (boundaryFullPowerDegree11Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree11Norm,boundaryFullPowerDegree11Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))=(boundaryFullPowerDegree11Block38Norm x).val+(boundaryFullPowerDegree11Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block38Norm x).property (boundaryFullPowerDegree11Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block38Norm,boundaryFullPowerDegree11Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))))=(boundaryFullPowerDegree11Block36Norm x).val+(boundaryFullPowerDegree11Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block36Norm x).property (boundaryFullPowerDegree11Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block36Norm,boundaryFullPowerDegree11Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x)))))))))+(((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x)))))))))+(((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))))))=(boundaryFullPowerDegree11Block31Norm x).val+(boundaryFullPowerDegree11Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block31Norm x).property (boundaryFullPowerDegree11Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block31Norm,boundaryFullPowerDegree11Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree11Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x)))))))))+(((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x)))))))))))+(((((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x)))))))))+(((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x)))))))))+(((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x)))))))))))+(((((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x)))))))))+(((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x))))))))))))=(boundaryFullPowerDegree11Block21Norm x).val+(boundaryFullPowerDegree11Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree11Block21Norm x).property (boundaryFullPowerDegree11Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block21Norm,boundaryFullPowerDegree11Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree11Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 11 x=c} := by

  have he0 : boundaryFullPowerRow77 11 x=((((((((((boundaryRePowerRow77_0 11 x)+(boundaryRePowerRow77_1 11 x)))+(((boundaryRePowerRow77_2 11 x)+(((boundaryRePowerRow77_3 11 x)+(boundaryRePowerRow77_4 11 x)))))))+(((((boundaryRePowerRow77_5 11 x)+(((boundaryRePowerRow77_6 11 x)+(boundaryRePowerRow77_7 11 x)))))+(((boundaryRePowerRow77_8 11 x)+(((boundaryRePowerRow77_9 11 x)+(boundaryRePowerRow77_10 11 x)))))))))+(((((((boundaryRePowerRow77_11 11 x)+(((boundaryRePowerRow77_12 11 x)+(boundaryRePowerRow77_13 11 x)))))+(((boundaryRePowerRow77_14 11 x)+(((boundaryRePowerRow77_15 11 x)+(boundaryRePowerRow77_16 11 x)))))))+(((((boundaryRePowerRow77_17 11 x)+(((boundaryRePowerRow77_18 11 x)+(boundaryRePowerRow77_19 11 x)))))+(((boundaryRePowerRow77_20 11 x)+(((boundaryRePowerRow77_21 11 x)+(boundaryRePowerRow77_22 11 x)))))))))))+(((((((((boundaryImPowerRow77_0 11 x)+(boundaryImPowerRow77_1 11 x)))+(((boundaryImPowerRow77_2 11 x)+(((boundaryImPowerRow77_3 11 x)+(boundaryImPowerRow77_4 11 x)))))))+(((((boundaryImPowerRow77_5 11 x)+(((boundaryImPowerRow77_6 11 x)+(boundaryImPowerRow77_7 11 x)))))+(((boundaryImPowerRow77_8 11 x)+(((boundaryImPowerRow77_9 11 x)+(boundaryImPowerRow77_10 11 x)))))))))+(((((((boundaryImPowerRow77_11 11 x)+(((boundaryImPowerRow77_12 11 x)+(boundaryImPowerRow77_13 11 x)))))+(((boundaryImPowerRow77_14 11 x)+(((boundaryImPowerRow77_15 11 x)+(boundaryImPowerRow77_16 11 x)))))))+(((((boundaryImPowerRow77_17 11 x)+(((boundaryImPowerRow77_18 11 x)+(boundaryImPowerRow77_19 11 x)))))+(((boundaryImPowerRow77_20 11 x)+(((boundaryImPowerRow77_21 11 x)+(boundaryLowPowerRow77 11 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree11Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree11Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
