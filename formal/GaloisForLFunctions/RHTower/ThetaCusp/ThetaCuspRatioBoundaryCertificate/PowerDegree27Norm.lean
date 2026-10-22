import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree27Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree27Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x))=c} := by

  have he : ((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x))=(boundaryRePowerRow77_0Degree27Norm x).val+(boundaryRePowerRow77_1Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree27Norm x).property (boundaryRePowerRow77_1Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree27Norm,boundaryRePowerRow77_1Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x))=c} := by

  have he : ((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x))=(boundaryRePowerRow77_3Degree27Norm x).val+(boundaryRePowerRow77_4Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree27Norm x).property (boundaryRePowerRow77_4Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree27Norm,boundaryRePowerRow77_4Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x))))=(boundaryRePowerRow77_2Degree27Norm x).val+(boundaryFullPowerDegree27Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree27Norm x).property (boundaryFullPowerDegree27Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree27Norm,boundaryFullPowerDegree27Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x))))))=(boundaryFullPowerDegree27Block0Norm x).val+(boundaryFullPowerDegree27Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block0Norm x).property (boundaryFullPowerDegree27Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block0Norm,boundaryFullPowerDegree27Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x))=c} := by

  have he : ((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x))=(boundaryRePowerRow77_6Degree27Norm x).val+(boundaryRePowerRow77_7Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree27Norm x).property (boundaryRePowerRow77_7Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree27Norm,boundaryRePowerRow77_7Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x))))=(boundaryRePowerRow77_5Degree27Norm x).val+(boundaryFullPowerDegree27Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree27Norm x).property (boundaryFullPowerDegree27Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree27Norm,boundaryFullPowerDegree27Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))=c} := by

  have he : ((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))=(boundaryRePowerRow77_9Degree27Norm x).val+(boundaryRePowerRow77_10Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree27Norm x).property (boundaryRePowerRow77_10Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree27Norm,boundaryRePowerRow77_10Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))))=(boundaryRePowerRow77_8Degree27Norm x).val+(boundaryFullPowerDegree27Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree27Norm x).property (boundaryFullPowerDegree27Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree27Norm,boundaryFullPowerDegree27Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))))))=(boundaryFullPowerDegree27Block5Norm x).val+(boundaryFullPowerDegree27Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block5Norm x).property (boundaryFullPowerDegree27Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block5Norm,boundaryFullPowerDegree27Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x))))))))=(boundaryFullPowerDegree27Block3Norm x).val+(boundaryFullPowerDegree27Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block3Norm x).property (boundaryFullPowerDegree27Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block3Norm,boundaryFullPowerDegree27Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x))=c} := by

  have he : ((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x))=(boundaryRePowerRow77_12Degree27Norm x).val+(boundaryRePowerRow77_13Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree27Norm x).property (boundaryRePowerRow77_13Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree27Norm,boundaryRePowerRow77_13Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x))))=(boundaryRePowerRow77_11Degree27Norm x).val+(boundaryFullPowerDegree27Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree27Norm x).property (boundaryFullPowerDegree27Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree27Norm,boundaryFullPowerDegree27Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x))=c} := by

  have he : ((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x))=(boundaryRePowerRow77_15Degree27Norm x).val+(boundaryRePowerRow77_16Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree27Norm x).property (boundaryRePowerRow77_16Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree27Norm,boundaryRePowerRow77_16Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x))))=(boundaryRePowerRow77_14Degree27Norm x).val+(boundaryFullPowerDegree27Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree27Norm x).property (boundaryFullPowerDegree27Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree27Norm,boundaryFullPowerDegree27Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x))))))=(boundaryFullPowerDegree27Block11Norm x).val+(boundaryFullPowerDegree27Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block11Norm x).property (boundaryFullPowerDegree27Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block11Norm,boundaryFullPowerDegree27Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x))=c} := by

  have he : ((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x))=(boundaryRePowerRow77_18Degree27Norm x).val+(boundaryRePowerRow77_19Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree27Norm x).property (boundaryRePowerRow77_19Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree27Norm,boundaryRePowerRow77_19Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x))))=(boundaryRePowerRow77_17Degree27Norm x).val+(boundaryFullPowerDegree27Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree27Norm x).property (boundaryFullPowerDegree27Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree27Norm,boundaryFullPowerDegree27Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))=c} := by

  have he : ((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))=(boundaryRePowerRow77_21Degree27Norm x).val+(boundaryRePowerRow77_22Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree27Norm x).property (boundaryRePowerRow77_22Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree27Norm,boundaryRePowerRow77_22Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))=(boundaryRePowerRow77_20Degree27Norm x).val+(boundaryFullPowerDegree27Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree27Norm x).property (boundaryFullPowerDegree27Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree27Norm,boundaryFullPowerDegree27Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))))=(boundaryFullPowerDegree27Block16Norm x).val+(boundaryFullPowerDegree27Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block16Norm x).property (boundaryFullPowerDegree27Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block16Norm,boundaryFullPowerDegree27Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))))))=(boundaryFullPowerDegree27Block14Norm x).val+(boundaryFullPowerDegree27Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block14Norm x).property (boundaryFullPowerDegree27Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block14Norm,boundaryFullPowerDegree27Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x)))))))))+(((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x)))))))))+(((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x))))))))))=(boundaryFullPowerDegree27Block9Norm x).val+(boundaryFullPowerDegree27Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block9Norm x).property (boundaryFullPowerDegree27Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block9Norm,boundaryFullPowerDegree27Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x))=c} := by

  have he : ((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x))=(boundaryImPowerRow77_0Degree27Norm x).val+(boundaryImPowerRow77_1Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree27Norm x).property (boundaryImPowerRow77_1Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree27Norm,boundaryImPowerRow77_1Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x))=c} := by

  have he : ((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x))=(boundaryImPowerRow77_3Degree27Norm x).val+(boundaryImPowerRow77_4Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree27Norm x).property (boundaryImPowerRow77_4Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree27Norm,boundaryImPowerRow77_4Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x))))=(boundaryImPowerRow77_2Degree27Norm x).val+(boundaryFullPowerDegree27Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree27Norm x).property (boundaryFullPowerDegree27Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree27Norm,boundaryFullPowerDegree27Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x))))))=(boundaryFullPowerDegree27Block22Norm x).val+(boundaryFullPowerDegree27Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block22Norm x).property (boundaryFullPowerDegree27Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block22Norm,boundaryFullPowerDegree27Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x))=c} := by

  have he : ((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x))=(boundaryImPowerRow77_6Degree27Norm x).val+(boundaryImPowerRow77_7Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree27Norm x).property (boundaryImPowerRow77_7Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree27Norm,boundaryImPowerRow77_7Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x))))=(boundaryImPowerRow77_5Degree27Norm x).val+(boundaryFullPowerDegree27Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree27Norm x).property (boundaryFullPowerDegree27Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree27Norm,boundaryFullPowerDegree27Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))=c} := by

  have he : ((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))=(boundaryImPowerRow77_9Degree27Norm x).val+(boundaryImPowerRow77_10Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree27Norm x).property (boundaryImPowerRow77_10Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree27Norm,boundaryImPowerRow77_10Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))))=(boundaryImPowerRow77_8Degree27Norm x).val+(boundaryFullPowerDegree27Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree27Norm x).property (boundaryFullPowerDegree27Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree27Norm,boundaryFullPowerDegree27Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))))))=(boundaryFullPowerDegree27Block27Norm x).val+(boundaryFullPowerDegree27Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block27Norm x).property (boundaryFullPowerDegree27Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block27Norm,boundaryFullPowerDegree27Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x))))))))=(boundaryFullPowerDegree27Block25Norm x).val+(boundaryFullPowerDegree27Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block25Norm x).property (boundaryFullPowerDegree27Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block25Norm,boundaryFullPowerDegree27Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x))=c} := by

  have he : ((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x))=(boundaryImPowerRow77_12Degree27Norm x).val+(boundaryImPowerRow77_13Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree27Norm x).property (boundaryImPowerRow77_13Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree27Norm,boundaryImPowerRow77_13Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x))))=(boundaryImPowerRow77_11Degree27Norm x).val+(boundaryFullPowerDegree27Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree27Norm x).property (boundaryFullPowerDegree27Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree27Norm,boundaryFullPowerDegree27Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x))=c} := by

  have he : ((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x))=(boundaryImPowerRow77_15Degree27Norm x).val+(boundaryImPowerRow77_16Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree27Norm x).property (boundaryImPowerRow77_16Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree27Norm,boundaryImPowerRow77_16Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x))))=(boundaryImPowerRow77_14Degree27Norm x).val+(boundaryFullPowerDegree27Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree27Norm x).property (boundaryFullPowerDegree27Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree27Norm,boundaryFullPowerDegree27Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x))))))=(boundaryFullPowerDegree27Block33Norm x).val+(boundaryFullPowerDegree27Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block33Norm x).property (boundaryFullPowerDegree27Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block33Norm,boundaryFullPowerDegree27Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x))=c} := by

  have he : ((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x))=(boundaryImPowerRow77_18Degree27Norm x).val+(boundaryImPowerRow77_19Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree27Norm x).property (boundaryImPowerRow77_19Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree27Norm,boundaryImPowerRow77_19Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x))))=(boundaryImPowerRow77_17Degree27Norm x).val+(boundaryFullPowerDegree27Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree27Norm x).property (boundaryFullPowerDegree27Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree27Norm,boundaryFullPowerDegree27Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))=c} := by

  have he : ((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))=(boundaryImPowerRow77_21Degree27Norm x).val+(boundaryLowPowerRow77Degree27Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree27Norm x).property (boundaryLowPowerRow77Degree27Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree27Norm,boundaryLowPowerRow77Degree27Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))=(boundaryImPowerRow77_20Degree27Norm x).val+(boundaryFullPowerDegree27Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree27Norm x).property (boundaryFullPowerDegree27Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree27Norm,boundaryFullPowerDegree27Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))=(boundaryFullPowerDegree27Block38Norm x).val+(boundaryFullPowerDegree27Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block38Norm x).property (boundaryFullPowerDegree27Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block38Norm,boundaryFullPowerDegree27Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))))=(boundaryFullPowerDegree27Block36Norm x).val+(boundaryFullPowerDegree27Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block36Norm x).property (boundaryFullPowerDegree27Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block36Norm,boundaryFullPowerDegree27Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x)))))))))+(((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x)))))))))+(((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))))))=(boundaryFullPowerDegree27Block31Norm x).val+(boundaryFullPowerDegree27Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block31Norm x).property (boundaryFullPowerDegree27Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block31Norm,boundaryFullPowerDegree27Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree27Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x)))))))))+(((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x)))))))))))+(((((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x)))))))))+(((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x)))))))))+(((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x)))))))))))+(((((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x)))))))))+(((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x))))))))))))=(boundaryFullPowerDegree27Block21Norm x).val+(boundaryFullPowerDegree27Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree27Block21Norm x).property (boundaryFullPowerDegree27Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block21Norm,boundaryFullPowerDegree27Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree27Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 27 x=c} := by

  have he0 : boundaryFullPowerRow77 27 x=((((((((((boundaryRePowerRow77_0 27 x)+(boundaryRePowerRow77_1 27 x)))+(((boundaryRePowerRow77_2 27 x)+(((boundaryRePowerRow77_3 27 x)+(boundaryRePowerRow77_4 27 x)))))))+(((((boundaryRePowerRow77_5 27 x)+(((boundaryRePowerRow77_6 27 x)+(boundaryRePowerRow77_7 27 x)))))+(((boundaryRePowerRow77_8 27 x)+(((boundaryRePowerRow77_9 27 x)+(boundaryRePowerRow77_10 27 x)))))))))+(((((((boundaryRePowerRow77_11 27 x)+(((boundaryRePowerRow77_12 27 x)+(boundaryRePowerRow77_13 27 x)))))+(((boundaryRePowerRow77_14 27 x)+(((boundaryRePowerRow77_15 27 x)+(boundaryRePowerRow77_16 27 x)))))))+(((((boundaryRePowerRow77_17 27 x)+(((boundaryRePowerRow77_18 27 x)+(boundaryRePowerRow77_19 27 x)))))+(((boundaryRePowerRow77_20 27 x)+(((boundaryRePowerRow77_21 27 x)+(boundaryRePowerRow77_22 27 x)))))))))))+(((((((((boundaryImPowerRow77_0 27 x)+(boundaryImPowerRow77_1 27 x)))+(((boundaryImPowerRow77_2 27 x)+(((boundaryImPowerRow77_3 27 x)+(boundaryImPowerRow77_4 27 x)))))))+(((((boundaryImPowerRow77_5 27 x)+(((boundaryImPowerRow77_6 27 x)+(boundaryImPowerRow77_7 27 x)))))+(((boundaryImPowerRow77_8 27 x)+(((boundaryImPowerRow77_9 27 x)+(boundaryImPowerRow77_10 27 x)))))))))+(((((((boundaryImPowerRow77_11 27 x)+(((boundaryImPowerRow77_12 27 x)+(boundaryImPowerRow77_13 27 x)))))+(((boundaryImPowerRow77_14 27 x)+(((boundaryImPowerRow77_15 27 x)+(boundaryImPowerRow77_16 27 x)))))))+(((((boundaryImPowerRow77_17 27 x)+(((boundaryImPowerRow77_18 27 x)+(boundaryImPowerRow77_19 27 x)))))+(((boundaryImPowerRow77_20 27 x)+(((boundaryImPowerRow77_21 27 x)+(boundaryLowPowerRow77 27 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree27Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree27Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
