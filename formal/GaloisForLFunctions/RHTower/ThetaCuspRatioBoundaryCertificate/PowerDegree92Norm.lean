import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree92Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree92Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x))=c} := by

  have he : ((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x))=(boundaryRePowerRow77_0Degree92Norm x).val+(boundaryRePowerRow77_1Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree92Norm x).property (boundaryRePowerRow77_1Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree92Norm,boundaryRePowerRow77_1Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x))=c} := by

  have he : ((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x))=(boundaryRePowerRow77_3Degree92Norm x).val+(boundaryRePowerRow77_4Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree92Norm x).property (boundaryRePowerRow77_4Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree92Norm,boundaryRePowerRow77_4Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x))))=(boundaryRePowerRow77_2Degree92Norm x).val+(boundaryFullPowerDegree92Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree92Norm x).property (boundaryFullPowerDegree92Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree92Norm,boundaryFullPowerDegree92Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x))))))=(boundaryFullPowerDegree92Block0Norm x).val+(boundaryFullPowerDegree92Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block0Norm x).property (boundaryFullPowerDegree92Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block0Norm,boundaryFullPowerDegree92Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x))=c} := by

  have he : ((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x))=(boundaryRePowerRow77_6Degree92Norm x).val+(boundaryRePowerRow77_7Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree92Norm x).property (boundaryRePowerRow77_7Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree92Norm,boundaryRePowerRow77_7Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x))))=(boundaryRePowerRow77_5Degree92Norm x).val+(boundaryFullPowerDegree92Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree92Norm x).property (boundaryFullPowerDegree92Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree92Norm,boundaryFullPowerDegree92Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))=c} := by

  have he : ((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))=(boundaryRePowerRow77_9Degree92Norm x).val+(boundaryRePowerRow77_10Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree92Norm x).property (boundaryRePowerRow77_10Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree92Norm,boundaryRePowerRow77_10Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))))=(boundaryRePowerRow77_8Degree92Norm x).val+(boundaryFullPowerDegree92Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree92Norm x).property (boundaryFullPowerDegree92Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree92Norm,boundaryFullPowerDegree92Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))))))=(boundaryFullPowerDegree92Block5Norm x).val+(boundaryFullPowerDegree92Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block5Norm x).property (boundaryFullPowerDegree92Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block5Norm,boundaryFullPowerDegree92Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x))))))))=(boundaryFullPowerDegree92Block3Norm x).val+(boundaryFullPowerDegree92Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block3Norm x).property (boundaryFullPowerDegree92Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block3Norm,boundaryFullPowerDegree92Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x))=c} := by

  have he : ((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x))=(boundaryRePowerRow77_12Degree92Norm x).val+(boundaryRePowerRow77_13Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree92Norm x).property (boundaryRePowerRow77_13Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree92Norm,boundaryRePowerRow77_13Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x))))=(boundaryRePowerRow77_11Degree92Norm x).val+(boundaryFullPowerDegree92Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree92Norm x).property (boundaryFullPowerDegree92Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree92Norm,boundaryFullPowerDegree92Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x))=c} := by

  have he : ((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x))=(boundaryRePowerRow77_15Degree92Norm x).val+(boundaryRePowerRow77_16Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree92Norm x).property (boundaryRePowerRow77_16Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree92Norm,boundaryRePowerRow77_16Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x))))=(boundaryRePowerRow77_14Degree92Norm x).val+(boundaryFullPowerDegree92Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree92Norm x).property (boundaryFullPowerDegree92Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree92Norm,boundaryFullPowerDegree92Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x))))))=(boundaryFullPowerDegree92Block11Norm x).val+(boundaryFullPowerDegree92Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block11Norm x).property (boundaryFullPowerDegree92Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block11Norm,boundaryFullPowerDegree92Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x))=c} := by

  have he : ((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x))=(boundaryRePowerRow77_18Degree92Norm x).val+(boundaryRePowerRow77_19Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree92Norm x).property (boundaryRePowerRow77_19Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree92Norm,boundaryRePowerRow77_19Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x))))=(boundaryRePowerRow77_17Degree92Norm x).val+(boundaryFullPowerDegree92Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree92Norm x).property (boundaryFullPowerDegree92Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree92Norm,boundaryFullPowerDegree92Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))=c} := by

  have he : ((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))=(boundaryRePowerRow77_21Degree92Norm x).val+(boundaryRePowerRow77_22Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree92Norm x).property (boundaryRePowerRow77_22Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree92Norm,boundaryRePowerRow77_22Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))=(boundaryRePowerRow77_20Degree92Norm x).val+(boundaryFullPowerDegree92Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree92Norm x).property (boundaryFullPowerDegree92Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree92Norm,boundaryFullPowerDegree92Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))))=(boundaryFullPowerDegree92Block16Norm x).val+(boundaryFullPowerDegree92Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block16Norm x).property (boundaryFullPowerDegree92Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block16Norm,boundaryFullPowerDegree92Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))))))=(boundaryFullPowerDegree92Block14Norm x).val+(boundaryFullPowerDegree92Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block14Norm x).property (boundaryFullPowerDegree92Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block14Norm,boundaryFullPowerDegree92Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x)))))))))+(((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x)))))))))+(((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x))))))))))=(boundaryFullPowerDegree92Block9Norm x).val+(boundaryFullPowerDegree92Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block9Norm x).property (boundaryFullPowerDegree92Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block9Norm,boundaryFullPowerDegree92Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x))=c} := by

  have he : ((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x))=(boundaryImPowerRow77_0Degree92Norm x).val+(boundaryImPowerRow77_1Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree92Norm x).property (boundaryImPowerRow77_1Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree92Norm,boundaryImPowerRow77_1Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x))=c} := by

  have he : ((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x))=(boundaryImPowerRow77_3Degree92Norm x).val+(boundaryImPowerRow77_4Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree92Norm x).property (boundaryImPowerRow77_4Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree92Norm,boundaryImPowerRow77_4Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x))))=(boundaryImPowerRow77_2Degree92Norm x).val+(boundaryFullPowerDegree92Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree92Norm x).property (boundaryFullPowerDegree92Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree92Norm,boundaryFullPowerDegree92Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x))))))=(boundaryFullPowerDegree92Block22Norm x).val+(boundaryFullPowerDegree92Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block22Norm x).property (boundaryFullPowerDegree92Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block22Norm,boundaryFullPowerDegree92Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x))=c} := by

  have he : ((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x))=(boundaryImPowerRow77_6Degree92Norm x).val+(boundaryImPowerRow77_7Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree92Norm x).property (boundaryImPowerRow77_7Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree92Norm,boundaryImPowerRow77_7Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x))))=(boundaryImPowerRow77_5Degree92Norm x).val+(boundaryFullPowerDegree92Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree92Norm x).property (boundaryFullPowerDegree92Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree92Norm,boundaryFullPowerDegree92Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))=c} := by

  have he : ((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))=(boundaryImPowerRow77_9Degree92Norm x).val+(boundaryImPowerRow77_10Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree92Norm x).property (boundaryImPowerRow77_10Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree92Norm,boundaryImPowerRow77_10Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))))=(boundaryImPowerRow77_8Degree92Norm x).val+(boundaryFullPowerDegree92Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree92Norm x).property (boundaryFullPowerDegree92Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree92Norm,boundaryFullPowerDegree92Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))))))=(boundaryFullPowerDegree92Block27Norm x).val+(boundaryFullPowerDegree92Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block27Norm x).property (boundaryFullPowerDegree92Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block27Norm,boundaryFullPowerDegree92Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x))))))))=(boundaryFullPowerDegree92Block25Norm x).val+(boundaryFullPowerDegree92Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block25Norm x).property (boundaryFullPowerDegree92Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block25Norm,boundaryFullPowerDegree92Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x))=c} := by

  have he : ((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x))=(boundaryImPowerRow77_12Degree92Norm x).val+(boundaryImPowerRow77_13Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree92Norm x).property (boundaryImPowerRow77_13Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree92Norm,boundaryImPowerRow77_13Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x))))=(boundaryImPowerRow77_11Degree92Norm x).val+(boundaryFullPowerDegree92Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree92Norm x).property (boundaryFullPowerDegree92Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree92Norm,boundaryFullPowerDegree92Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x))=c} := by

  have he : ((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x))=(boundaryImPowerRow77_15Degree92Norm x).val+(boundaryImPowerRow77_16Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree92Norm x).property (boundaryImPowerRow77_16Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree92Norm,boundaryImPowerRow77_16Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x))))=(boundaryImPowerRow77_14Degree92Norm x).val+(boundaryFullPowerDegree92Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree92Norm x).property (boundaryFullPowerDegree92Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree92Norm,boundaryFullPowerDegree92Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x))))))=(boundaryFullPowerDegree92Block33Norm x).val+(boundaryFullPowerDegree92Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block33Norm x).property (boundaryFullPowerDegree92Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block33Norm,boundaryFullPowerDegree92Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x))=c} := by

  have he : ((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x))=(boundaryImPowerRow77_18Degree92Norm x).val+(boundaryImPowerRow77_19Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree92Norm x).property (boundaryImPowerRow77_19Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree92Norm,boundaryImPowerRow77_19Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x))))=(boundaryImPowerRow77_17Degree92Norm x).val+(boundaryFullPowerDegree92Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree92Norm x).property (boundaryFullPowerDegree92Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree92Norm,boundaryFullPowerDegree92Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))=c} := by

  have he : ((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))=(boundaryImPowerRow77_21Degree92Norm x).val+(boundaryLowPowerRow77Degree92Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree92Norm x).property (boundaryLowPowerRow77Degree92Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree92Norm,boundaryLowPowerRow77Degree92Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))=(boundaryImPowerRow77_20Degree92Norm x).val+(boundaryFullPowerDegree92Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree92Norm x).property (boundaryFullPowerDegree92Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree92Norm,boundaryFullPowerDegree92Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))=(boundaryFullPowerDegree92Block38Norm x).val+(boundaryFullPowerDegree92Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block38Norm x).property (boundaryFullPowerDegree92Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block38Norm,boundaryFullPowerDegree92Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))))=(boundaryFullPowerDegree92Block36Norm x).val+(boundaryFullPowerDegree92Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block36Norm x).property (boundaryFullPowerDegree92Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block36Norm,boundaryFullPowerDegree92Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x)))))))))+(((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x)))))))))+(((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))))))=(boundaryFullPowerDegree92Block31Norm x).val+(boundaryFullPowerDegree92Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block31Norm x).property (boundaryFullPowerDegree92Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block31Norm,boundaryFullPowerDegree92Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree92Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x)))))))))+(((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x)))))))))))+(((((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x)))))))))+(((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x)))))))))+(((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x)))))))))))+(((((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x)))))))))+(((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x))))))))))))=(boundaryFullPowerDegree92Block21Norm x).val+(boundaryFullPowerDegree92Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree92Block21Norm x).property (boundaryFullPowerDegree92Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block21Norm,boundaryFullPowerDegree92Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree92Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 92 x=c} := by

  have he0 : boundaryFullPowerRow77 92 x=((((((((((boundaryRePowerRow77_0 92 x)+(boundaryRePowerRow77_1 92 x)))+(((boundaryRePowerRow77_2 92 x)+(((boundaryRePowerRow77_3 92 x)+(boundaryRePowerRow77_4 92 x)))))))+(((((boundaryRePowerRow77_5 92 x)+(((boundaryRePowerRow77_6 92 x)+(boundaryRePowerRow77_7 92 x)))))+(((boundaryRePowerRow77_8 92 x)+(((boundaryRePowerRow77_9 92 x)+(boundaryRePowerRow77_10 92 x)))))))))+(((((((boundaryRePowerRow77_11 92 x)+(((boundaryRePowerRow77_12 92 x)+(boundaryRePowerRow77_13 92 x)))))+(((boundaryRePowerRow77_14 92 x)+(((boundaryRePowerRow77_15 92 x)+(boundaryRePowerRow77_16 92 x)))))))+(((((boundaryRePowerRow77_17 92 x)+(((boundaryRePowerRow77_18 92 x)+(boundaryRePowerRow77_19 92 x)))))+(((boundaryRePowerRow77_20 92 x)+(((boundaryRePowerRow77_21 92 x)+(boundaryRePowerRow77_22 92 x)))))))))))+(((((((((boundaryImPowerRow77_0 92 x)+(boundaryImPowerRow77_1 92 x)))+(((boundaryImPowerRow77_2 92 x)+(((boundaryImPowerRow77_3 92 x)+(boundaryImPowerRow77_4 92 x)))))))+(((((boundaryImPowerRow77_5 92 x)+(((boundaryImPowerRow77_6 92 x)+(boundaryImPowerRow77_7 92 x)))))+(((boundaryImPowerRow77_8 92 x)+(((boundaryImPowerRow77_9 92 x)+(boundaryImPowerRow77_10 92 x)))))))))+(((((((boundaryImPowerRow77_11 92 x)+(((boundaryImPowerRow77_12 92 x)+(boundaryImPowerRow77_13 92 x)))))+(((boundaryImPowerRow77_14 92 x)+(((boundaryImPowerRow77_15 92 x)+(boundaryImPowerRow77_16 92 x)))))))+(((((boundaryImPowerRow77_17 92 x)+(((boundaryImPowerRow77_18 92 x)+(boundaryImPowerRow77_19 92 x)))))+(((boundaryImPowerRow77_20 92 x)+(((boundaryImPowerRow77_21 92 x)+(boundaryLowPowerRow77 92 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree92Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree92Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
