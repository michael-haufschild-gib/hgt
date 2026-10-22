import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree91Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree91Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x))=c} := by

  have he : ((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x))=(boundaryRePowerRow77_0Degree91Norm x).val+(boundaryRePowerRow77_1Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree91Norm x).property (boundaryRePowerRow77_1Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree91Norm,boundaryRePowerRow77_1Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x))=c} := by

  have he : ((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x))=(boundaryRePowerRow77_3Degree91Norm x).val+(boundaryRePowerRow77_4Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree91Norm x).property (boundaryRePowerRow77_4Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree91Norm,boundaryRePowerRow77_4Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x))))=(boundaryRePowerRow77_2Degree91Norm x).val+(boundaryFullPowerDegree91Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree91Norm x).property (boundaryFullPowerDegree91Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree91Norm,boundaryFullPowerDegree91Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x))))))=(boundaryFullPowerDegree91Block0Norm x).val+(boundaryFullPowerDegree91Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block0Norm x).property (boundaryFullPowerDegree91Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block0Norm,boundaryFullPowerDegree91Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x))=c} := by

  have he : ((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x))=(boundaryRePowerRow77_6Degree91Norm x).val+(boundaryRePowerRow77_7Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree91Norm x).property (boundaryRePowerRow77_7Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree91Norm,boundaryRePowerRow77_7Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x))))=(boundaryRePowerRow77_5Degree91Norm x).val+(boundaryFullPowerDegree91Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree91Norm x).property (boundaryFullPowerDegree91Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree91Norm,boundaryFullPowerDegree91Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))=c} := by

  have he : ((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))=(boundaryRePowerRow77_9Degree91Norm x).val+(boundaryRePowerRow77_10Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree91Norm x).property (boundaryRePowerRow77_10Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree91Norm,boundaryRePowerRow77_10Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))))=(boundaryRePowerRow77_8Degree91Norm x).val+(boundaryFullPowerDegree91Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree91Norm x).property (boundaryFullPowerDegree91Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree91Norm,boundaryFullPowerDegree91Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))))))=(boundaryFullPowerDegree91Block5Norm x).val+(boundaryFullPowerDegree91Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block5Norm x).property (boundaryFullPowerDegree91Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block5Norm,boundaryFullPowerDegree91Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x))))))))=(boundaryFullPowerDegree91Block3Norm x).val+(boundaryFullPowerDegree91Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block3Norm x).property (boundaryFullPowerDegree91Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block3Norm,boundaryFullPowerDegree91Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x))=c} := by

  have he : ((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x))=(boundaryRePowerRow77_12Degree91Norm x).val+(boundaryRePowerRow77_13Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree91Norm x).property (boundaryRePowerRow77_13Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree91Norm,boundaryRePowerRow77_13Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x))))=(boundaryRePowerRow77_11Degree91Norm x).val+(boundaryFullPowerDegree91Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree91Norm x).property (boundaryFullPowerDegree91Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree91Norm,boundaryFullPowerDegree91Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x))=c} := by

  have he : ((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x))=(boundaryRePowerRow77_15Degree91Norm x).val+(boundaryRePowerRow77_16Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree91Norm x).property (boundaryRePowerRow77_16Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree91Norm,boundaryRePowerRow77_16Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x))))=(boundaryRePowerRow77_14Degree91Norm x).val+(boundaryFullPowerDegree91Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree91Norm x).property (boundaryFullPowerDegree91Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree91Norm,boundaryFullPowerDegree91Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x))))))=(boundaryFullPowerDegree91Block11Norm x).val+(boundaryFullPowerDegree91Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block11Norm x).property (boundaryFullPowerDegree91Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block11Norm,boundaryFullPowerDegree91Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x))=c} := by

  have he : ((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x))=(boundaryRePowerRow77_18Degree91Norm x).val+(boundaryRePowerRow77_19Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree91Norm x).property (boundaryRePowerRow77_19Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree91Norm,boundaryRePowerRow77_19Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x))))=(boundaryRePowerRow77_17Degree91Norm x).val+(boundaryFullPowerDegree91Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree91Norm x).property (boundaryFullPowerDegree91Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree91Norm,boundaryFullPowerDegree91Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))=c} := by

  have he : ((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))=(boundaryRePowerRow77_21Degree91Norm x).val+(boundaryRePowerRow77_22Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree91Norm x).property (boundaryRePowerRow77_22Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree91Norm,boundaryRePowerRow77_22Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))=(boundaryRePowerRow77_20Degree91Norm x).val+(boundaryFullPowerDegree91Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree91Norm x).property (boundaryFullPowerDegree91Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree91Norm,boundaryFullPowerDegree91Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))))=(boundaryFullPowerDegree91Block16Norm x).val+(boundaryFullPowerDegree91Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block16Norm x).property (boundaryFullPowerDegree91Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block16Norm,boundaryFullPowerDegree91Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))))))=(boundaryFullPowerDegree91Block14Norm x).val+(boundaryFullPowerDegree91Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block14Norm x).property (boundaryFullPowerDegree91Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block14Norm,boundaryFullPowerDegree91Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x)))))))))+(((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x)))))))))+(((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x))))))))))=(boundaryFullPowerDegree91Block9Norm x).val+(boundaryFullPowerDegree91Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block9Norm x).property (boundaryFullPowerDegree91Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block9Norm,boundaryFullPowerDegree91Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x))=c} := by

  have he : ((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x))=(boundaryImPowerRow77_0Degree91Norm x).val+(boundaryImPowerRow77_1Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree91Norm x).property (boundaryImPowerRow77_1Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree91Norm,boundaryImPowerRow77_1Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x))=c} := by

  have he : ((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x))=(boundaryImPowerRow77_3Degree91Norm x).val+(boundaryImPowerRow77_4Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree91Norm x).property (boundaryImPowerRow77_4Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree91Norm,boundaryImPowerRow77_4Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x))))=(boundaryImPowerRow77_2Degree91Norm x).val+(boundaryFullPowerDegree91Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree91Norm x).property (boundaryFullPowerDegree91Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree91Norm,boundaryFullPowerDegree91Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x))))))=(boundaryFullPowerDegree91Block22Norm x).val+(boundaryFullPowerDegree91Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block22Norm x).property (boundaryFullPowerDegree91Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block22Norm,boundaryFullPowerDegree91Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x))=c} := by

  have he : ((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x))=(boundaryImPowerRow77_6Degree91Norm x).val+(boundaryImPowerRow77_7Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree91Norm x).property (boundaryImPowerRow77_7Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree91Norm,boundaryImPowerRow77_7Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x))))=(boundaryImPowerRow77_5Degree91Norm x).val+(boundaryFullPowerDegree91Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree91Norm x).property (boundaryFullPowerDegree91Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree91Norm,boundaryFullPowerDegree91Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))=c} := by

  have he : ((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))=(boundaryImPowerRow77_9Degree91Norm x).val+(boundaryImPowerRow77_10Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree91Norm x).property (boundaryImPowerRow77_10Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree91Norm,boundaryImPowerRow77_10Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))))=(boundaryImPowerRow77_8Degree91Norm x).val+(boundaryFullPowerDegree91Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree91Norm x).property (boundaryFullPowerDegree91Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree91Norm,boundaryFullPowerDegree91Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))))))=(boundaryFullPowerDegree91Block27Norm x).val+(boundaryFullPowerDegree91Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block27Norm x).property (boundaryFullPowerDegree91Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block27Norm,boundaryFullPowerDegree91Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x))))))))=(boundaryFullPowerDegree91Block25Norm x).val+(boundaryFullPowerDegree91Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block25Norm x).property (boundaryFullPowerDegree91Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block25Norm,boundaryFullPowerDegree91Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x))=c} := by

  have he : ((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x))=(boundaryImPowerRow77_12Degree91Norm x).val+(boundaryImPowerRow77_13Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree91Norm x).property (boundaryImPowerRow77_13Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree91Norm,boundaryImPowerRow77_13Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x))))=(boundaryImPowerRow77_11Degree91Norm x).val+(boundaryFullPowerDegree91Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree91Norm x).property (boundaryFullPowerDegree91Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree91Norm,boundaryFullPowerDegree91Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x))=c} := by

  have he : ((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x))=(boundaryImPowerRow77_15Degree91Norm x).val+(boundaryImPowerRow77_16Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree91Norm x).property (boundaryImPowerRow77_16Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree91Norm,boundaryImPowerRow77_16Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x))))=(boundaryImPowerRow77_14Degree91Norm x).val+(boundaryFullPowerDegree91Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree91Norm x).property (boundaryFullPowerDegree91Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree91Norm,boundaryFullPowerDegree91Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x))))))=(boundaryFullPowerDegree91Block33Norm x).val+(boundaryFullPowerDegree91Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block33Norm x).property (boundaryFullPowerDegree91Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block33Norm,boundaryFullPowerDegree91Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x))=c} := by

  have he : ((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x))=(boundaryImPowerRow77_18Degree91Norm x).val+(boundaryImPowerRow77_19Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree91Norm x).property (boundaryImPowerRow77_19Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree91Norm,boundaryImPowerRow77_19Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x))))=(boundaryImPowerRow77_17Degree91Norm x).val+(boundaryFullPowerDegree91Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree91Norm x).property (boundaryFullPowerDegree91Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree91Norm,boundaryFullPowerDegree91Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))=c} := by

  have he : ((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))=(boundaryImPowerRow77_21Degree91Norm x).val+(boundaryLowPowerRow77Degree91Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree91Norm x).property (boundaryLowPowerRow77Degree91Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree91Norm,boundaryLowPowerRow77Degree91Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))=(boundaryImPowerRow77_20Degree91Norm x).val+(boundaryFullPowerDegree91Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree91Norm x).property (boundaryFullPowerDegree91Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree91Norm,boundaryFullPowerDegree91Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))=(boundaryFullPowerDegree91Block38Norm x).val+(boundaryFullPowerDegree91Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block38Norm x).property (boundaryFullPowerDegree91Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block38Norm,boundaryFullPowerDegree91Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))))=(boundaryFullPowerDegree91Block36Norm x).val+(boundaryFullPowerDegree91Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block36Norm x).property (boundaryFullPowerDegree91Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block36Norm,boundaryFullPowerDegree91Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x)))))))))+(((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x)))))))))+(((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))))))=(boundaryFullPowerDegree91Block31Norm x).val+(boundaryFullPowerDegree91Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block31Norm x).property (boundaryFullPowerDegree91Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block31Norm,boundaryFullPowerDegree91Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree91Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x)))))))))+(((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x)))))))))))+(((((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x)))))))))+(((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x)))))))))+(((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x)))))))))))+(((((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x)))))))))+(((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x))))))))))))=(boundaryFullPowerDegree91Block21Norm x).val+(boundaryFullPowerDegree91Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree91Block21Norm x).property (boundaryFullPowerDegree91Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block21Norm,boundaryFullPowerDegree91Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree91Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 91 x=c} := by

  have he0 : boundaryFullPowerRow77 91 x=((((((((((boundaryRePowerRow77_0 91 x)+(boundaryRePowerRow77_1 91 x)))+(((boundaryRePowerRow77_2 91 x)+(((boundaryRePowerRow77_3 91 x)+(boundaryRePowerRow77_4 91 x)))))))+(((((boundaryRePowerRow77_5 91 x)+(((boundaryRePowerRow77_6 91 x)+(boundaryRePowerRow77_7 91 x)))))+(((boundaryRePowerRow77_8 91 x)+(((boundaryRePowerRow77_9 91 x)+(boundaryRePowerRow77_10 91 x)))))))))+(((((((boundaryRePowerRow77_11 91 x)+(((boundaryRePowerRow77_12 91 x)+(boundaryRePowerRow77_13 91 x)))))+(((boundaryRePowerRow77_14 91 x)+(((boundaryRePowerRow77_15 91 x)+(boundaryRePowerRow77_16 91 x)))))))+(((((boundaryRePowerRow77_17 91 x)+(((boundaryRePowerRow77_18 91 x)+(boundaryRePowerRow77_19 91 x)))))+(((boundaryRePowerRow77_20 91 x)+(((boundaryRePowerRow77_21 91 x)+(boundaryRePowerRow77_22 91 x)))))))))))+(((((((((boundaryImPowerRow77_0 91 x)+(boundaryImPowerRow77_1 91 x)))+(((boundaryImPowerRow77_2 91 x)+(((boundaryImPowerRow77_3 91 x)+(boundaryImPowerRow77_4 91 x)))))))+(((((boundaryImPowerRow77_5 91 x)+(((boundaryImPowerRow77_6 91 x)+(boundaryImPowerRow77_7 91 x)))))+(((boundaryImPowerRow77_8 91 x)+(((boundaryImPowerRow77_9 91 x)+(boundaryImPowerRow77_10 91 x)))))))))+(((((((boundaryImPowerRow77_11 91 x)+(((boundaryImPowerRow77_12 91 x)+(boundaryImPowerRow77_13 91 x)))))+(((boundaryImPowerRow77_14 91 x)+(((boundaryImPowerRow77_15 91 x)+(boundaryImPowerRow77_16 91 x)))))))+(((((boundaryImPowerRow77_17 91 x)+(((boundaryImPowerRow77_18 91 x)+(boundaryImPowerRow77_19 91 x)))))+(((boundaryImPowerRow77_20 91 x)+(((boundaryImPowerRow77_21 91 x)+(boundaryLowPowerRow77 91 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree91Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree91Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
