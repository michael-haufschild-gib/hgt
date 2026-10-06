import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree15Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree15Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x))=c} := by

  have he : ((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x))=(boundaryRePowerRow77_0Degree15Norm x).val+(boundaryRePowerRow77_1Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree15Norm x).property (boundaryRePowerRow77_1Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree15Norm,boundaryRePowerRow77_1Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x))=c} := by

  have he : ((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x))=(boundaryRePowerRow77_3Degree15Norm x).val+(boundaryRePowerRow77_4Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree15Norm x).property (boundaryRePowerRow77_4Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree15Norm,boundaryRePowerRow77_4Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x))))=(boundaryRePowerRow77_2Degree15Norm x).val+(boundaryFullPowerDegree15Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree15Norm x).property (boundaryFullPowerDegree15Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree15Norm,boundaryFullPowerDegree15Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x))))))=(boundaryFullPowerDegree15Block0Norm x).val+(boundaryFullPowerDegree15Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block0Norm x).property (boundaryFullPowerDegree15Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block0Norm,boundaryFullPowerDegree15Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x))=c} := by

  have he : ((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x))=(boundaryRePowerRow77_6Degree15Norm x).val+(boundaryRePowerRow77_7Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree15Norm x).property (boundaryRePowerRow77_7Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree15Norm,boundaryRePowerRow77_7Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x))))=(boundaryRePowerRow77_5Degree15Norm x).val+(boundaryFullPowerDegree15Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree15Norm x).property (boundaryFullPowerDegree15Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree15Norm,boundaryFullPowerDegree15Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))=c} := by

  have he : ((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))=(boundaryRePowerRow77_9Degree15Norm x).val+(boundaryRePowerRow77_10Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree15Norm x).property (boundaryRePowerRow77_10Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree15Norm,boundaryRePowerRow77_10Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))))=(boundaryRePowerRow77_8Degree15Norm x).val+(boundaryFullPowerDegree15Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree15Norm x).property (boundaryFullPowerDegree15Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree15Norm,boundaryFullPowerDegree15Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))))))=(boundaryFullPowerDegree15Block5Norm x).val+(boundaryFullPowerDegree15Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block5Norm x).property (boundaryFullPowerDegree15Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block5Norm,boundaryFullPowerDegree15Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x))))))))=(boundaryFullPowerDegree15Block3Norm x).val+(boundaryFullPowerDegree15Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block3Norm x).property (boundaryFullPowerDegree15Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block3Norm,boundaryFullPowerDegree15Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x))=c} := by

  have he : ((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x))=(boundaryRePowerRow77_12Degree15Norm x).val+(boundaryRePowerRow77_13Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree15Norm x).property (boundaryRePowerRow77_13Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree15Norm,boundaryRePowerRow77_13Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x))))=(boundaryRePowerRow77_11Degree15Norm x).val+(boundaryFullPowerDegree15Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree15Norm x).property (boundaryFullPowerDegree15Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree15Norm,boundaryFullPowerDegree15Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x))=c} := by

  have he : ((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x))=(boundaryRePowerRow77_15Degree15Norm x).val+(boundaryRePowerRow77_16Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree15Norm x).property (boundaryRePowerRow77_16Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree15Norm,boundaryRePowerRow77_16Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x))))=(boundaryRePowerRow77_14Degree15Norm x).val+(boundaryFullPowerDegree15Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree15Norm x).property (boundaryFullPowerDegree15Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree15Norm,boundaryFullPowerDegree15Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x))))))=(boundaryFullPowerDegree15Block11Norm x).val+(boundaryFullPowerDegree15Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block11Norm x).property (boundaryFullPowerDegree15Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block11Norm,boundaryFullPowerDegree15Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x))=c} := by

  have he : ((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x))=(boundaryRePowerRow77_18Degree15Norm x).val+(boundaryRePowerRow77_19Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree15Norm x).property (boundaryRePowerRow77_19Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree15Norm,boundaryRePowerRow77_19Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x))))=(boundaryRePowerRow77_17Degree15Norm x).val+(boundaryFullPowerDegree15Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree15Norm x).property (boundaryFullPowerDegree15Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree15Norm,boundaryFullPowerDegree15Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))=c} := by

  have he : ((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))=(boundaryRePowerRow77_21Degree15Norm x).val+(boundaryRePowerRow77_22Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree15Norm x).property (boundaryRePowerRow77_22Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree15Norm,boundaryRePowerRow77_22Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))=(boundaryRePowerRow77_20Degree15Norm x).val+(boundaryFullPowerDegree15Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree15Norm x).property (boundaryFullPowerDegree15Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree15Norm,boundaryFullPowerDegree15Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))))=(boundaryFullPowerDegree15Block16Norm x).val+(boundaryFullPowerDegree15Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block16Norm x).property (boundaryFullPowerDegree15Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block16Norm,boundaryFullPowerDegree15Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))))))=(boundaryFullPowerDegree15Block14Norm x).val+(boundaryFullPowerDegree15Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block14Norm x).property (boundaryFullPowerDegree15Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block14Norm,boundaryFullPowerDegree15Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x)))))))))+(((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x)))))))))+(((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x))))))))))=(boundaryFullPowerDegree15Block9Norm x).val+(boundaryFullPowerDegree15Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block9Norm x).property (boundaryFullPowerDegree15Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block9Norm,boundaryFullPowerDegree15Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x))=c} := by

  have he : ((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x))=(boundaryImPowerRow77_0Degree15Norm x).val+(boundaryImPowerRow77_1Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree15Norm x).property (boundaryImPowerRow77_1Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree15Norm,boundaryImPowerRow77_1Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x))=c} := by

  have he : ((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x))=(boundaryImPowerRow77_3Degree15Norm x).val+(boundaryImPowerRow77_4Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree15Norm x).property (boundaryImPowerRow77_4Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree15Norm,boundaryImPowerRow77_4Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x))))=(boundaryImPowerRow77_2Degree15Norm x).val+(boundaryFullPowerDegree15Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree15Norm x).property (boundaryFullPowerDegree15Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree15Norm,boundaryFullPowerDegree15Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x))))))=(boundaryFullPowerDegree15Block22Norm x).val+(boundaryFullPowerDegree15Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block22Norm x).property (boundaryFullPowerDegree15Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block22Norm,boundaryFullPowerDegree15Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x))=c} := by

  have he : ((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x))=(boundaryImPowerRow77_6Degree15Norm x).val+(boundaryImPowerRow77_7Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree15Norm x).property (boundaryImPowerRow77_7Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree15Norm,boundaryImPowerRow77_7Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x))))=(boundaryImPowerRow77_5Degree15Norm x).val+(boundaryFullPowerDegree15Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree15Norm x).property (boundaryFullPowerDegree15Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree15Norm,boundaryFullPowerDegree15Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))=c} := by

  have he : ((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))=(boundaryImPowerRow77_9Degree15Norm x).val+(boundaryImPowerRow77_10Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree15Norm x).property (boundaryImPowerRow77_10Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree15Norm,boundaryImPowerRow77_10Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))))=(boundaryImPowerRow77_8Degree15Norm x).val+(boundaryFullPowerDegree15Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree15Norm x).property (boundaryFullPowerDegree15Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree15Norm,boundaryFullPowerDegree15Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))))))=(boundaryFullPowerDegree15Block27Norm x).val+(boundaryFullPowerDegree15Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block27Norm x).property (boundaryFullPowerDegree15Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block27Norm,boundaryFullPowerDegree15Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x))))))))=(boundaryFullPowerDegree15Block25Norm x).val+(boundaryFullPowerDegree15Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block25Norm x).property (boundaryFullPowerDegree15Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block25Norm,boundaryFullPowerDegree15Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x))=c} := by

  have he : ((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x))=(boundaryImPowerRow77_12Degree15Norm x).val+(boundaryImPowerRow77_13Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree15Norm x).property (boundaryImPowerRow77_13Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree15Norm,boundaryImPowerRow77_13Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x))))=(boundaryImPowerRow77_11Degree15Norm x).val+(boundaryFullPowerDegree15Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree15Norm x).property (boundaryFullPowerDegree15Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree15Norm,boundaryFullPowerDegree15Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x))=c} := by

  have he : ((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x))=(boundaryImPowerRow77_15Degree15Norm x).val+(boundaryImPowerRow77_16Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree15Norm x).property (boundaryImPowerRow77_16Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree15Norm,boundaryImPowerRow77_16Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x))))=(boundaryImPowerRow77_14Degree15Norm x).val+(boundaryFullPowerDegree15Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree15Norm x).property (boundaryFullPowerDegree15Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree15Norm,boundaryFullPowerDegree15Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x))))))=(boundaryFullPowerDegree15Block33Norm x).val+(boundaryFullPowerDegree15Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block33Norm x).property (boundaryFullPowerDegree15Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block33Norm,boundaryFullPowerDegree15Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x))=c} := by

  have he : ((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x))=(boundaryImPowerRow77_18Degree15Norm x).val+(boundaryImPowerRow77_19Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree15Norm x).property (boundaryImPowerRow77_19Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree15Norm,boundaryImPowerRow77_19Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x))))=(boundaryImPowerRow77_17Degree15Norm x).val+(boundaryFullPowerDegree15Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree15Norm x).property (boundaryFullPowerDegree15Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree15Norm,boundaryFullPowerDegree15Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))=c} := by

  have he : ((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))=(boundaryImPowerRow77_21Degree15Norm x).val+(boundaryLowPowerRow77Degree15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree15Norm x).property (boundaryLowPowerRow77Degree15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree15Norm,boundaryLowPowerRow77Degree15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))=(boundaryImPowerRow77_20Degree15Norm x).val+(boundaryFullPowerDegree15Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree15Norm x).property (boundaryFullPowerDegree15Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree15Norm,boundaryFullPowerDegree15Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))=(boundaryFullPowerDegree15Block38Norm x).val+(boundaryFullPowerDegree15Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block38Norm x).property (boundaryFullPowerDegree15Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block38Norm,boundaryFullPowerDegree15Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))))=(boundaryFullPowerDegree15Block36Norm x).val+(boundaryFullPowerDegree15Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block36Norm x).property (boundaryFullPowerDegree15Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block36Norm,boundaryFullPowerDegree15Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x)))))))))+(((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x)))))))))+(((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))))))=(boundaryFullPowerDegree15Block31Norm x).val+(boundaryFullPowerDegree15Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block31Norm x).property (boundaryFullPowerDegree15Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block31Norm,boundaryFullPowerDegree15Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree15Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x)))))))))+(((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x)))))))))))+(((((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x)))))))))+(((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x)))))))))+(((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x)))))))))))+(((((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x)))))))))+(((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x))))))))))))=(boundaryFullPowerDegree15Block21Norm x).val+(boundaryFullPowerDegree15Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree15Block21Norm x).property (boundaryFullPowerDegree15Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block21Norm,boundaryFullPowerDegree15Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree15Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 15 x=c} := by

  have he0 : boundaryFullPowerRow77 15 x=((((((((((boundaryRePowerRow77_0 15 x)+(boundaryRePowerRow77_1 15 x)))+(((boundaryRePowerRow77_2 15 x)+(((boundaryRePowerRow77_3 15 x)+(boundaryRePowerRow77_4 15 x)))))))+(((((boundaryRePowerRow77_5 15 x)+(((boundaryRePowerRow77_6 15 x)+(boundaryRePowerRow77_7 15 x)))))+(((boundaryRePowerRow77_8 15 x)+(((boundaryRePowerRow77_9 15 x)+(boundaryRePowerRow77_10 15 x)))))))))+(((((((boundaryRePowerRow77_11 15 x)+(((boundaryRePowerRow77_12 15 x)+(boundaryRePowerRow77_13 15 x)))))+(((boundaryRePowerRow77_14 15 x)+(((boundaryRePowerRow77_15 15 x)+(boundaryRePowerRow77_16 15 x)))))))+(((((boundaryRePowerRow77_17 15 x)+(((boundaryRePowerRow77_18 15 x)+(boundaryRePowerRow77_19 15 x)))))+(((boundaryRePowerRow77_20 15 x)+(((boundaryRePowerRow77_21 15 x)+(boundaryRePowerRow77_22 15 x)))))))))))+(((((((((boundaryImPowerRow77_0 15 x)+(boundaryImPowerRow77_1 15 x)))+(((boundaryImPowerRow77_2 15 x)+(((boundaryImPowerRow77_3 15 x)+(boundaryImPowerRow77_4 15 x)))))))+(((((boundaryImPowerRow77_5 15 x)+(((boundaryImPowerRow77_6 15 x)+(boundaryImPowerRow77_7 15 x)))))+(((boundaryImPowerRow77_8 15 x)+(((boundaryImPowerRow77_9 15 x)+(boundaryImPowerRow77_10 15 x)))))))))+(((((((boundaryImPowerRow77_11 15 x)+(((boundaryImPowerRow77_12 15 x)+(boundaryImPowerRow77_13 15 x)))))+(((boundaryImPowerRow77_14 15 x)+(((boundaryImPowerRow77_15 15 x)+(boundaryImPowerRow77_16 15 x)))))))+(((((boundaryImPowerRow77_17 15 x)+(((boundaryImPowerRow77_18 15 x)+(boundaryImPowerRow77_19 15 x)))))+(((boundaryImPowerRow77_20 15 x)+(((boundaryImPowerRow77_21 15 x)+(boundaryLowPowerRow77 15 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree15Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree15Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
