import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree70Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree70Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x))=c} := by

  have he : ((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x))=(boundaryRePowerRow77_0Degree70Norm x).val+(boundaryRePowerRow77_1Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree70Norm x).property (boundaryRePowerRow77_1Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree70Norm,boundaryRePowerRow77_1Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x))=c} := by

  have he : ((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x))=(boundaryRePowerRow77_3Degree70Norm x).val+(boundaryRePowerRow77_4Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree70Norm x).property (boundaryRePowerRow77_4Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree70Norm,boundaryRePowerRow77_4Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x))))=(boundaryRePowerRow77_2Degree70Norm x).val+(boundaryFullPowerDegree70Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree70Norm x).property (boundaryFullPowerDegree70Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree70Norm,boundaryFullPowerDegree70Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x))))))=(boundaryFullPowerDegree70Block0Norm x).val+(boundaryFullPowerDegree70Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block0Norm x).property (boundaryFullPowerDegree70Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block0Norm,boundaryFullPowerDegree70Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x))=c} := by

  have he : ((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x))=(boundaryRePowerRow77_6Degree70Norm x).val+(boundaryRePowerRow77_7Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree70Norm x).property (boundaryRePowerRow77_7Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree70Norm,boundaryRePowerRow77_7Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x))))=(boundaryRePowerRow77_5Degree70Norm x).val+(boundaryFullPowerDegree70Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree70Norm x).property (boundaryFullPowerDegree70Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree70Norm,boundaryFullPowerDegree70Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))=c} := by

  have he : ((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))=(boundaryRePowerRow77_9Degree70Norm x).val+(boundaryRePowerRow77_10Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree70Norm x).property (boundaryRePowerRow77_10Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree70Norm,boundaryRePowerRow77_10Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))))=(boundaryRePowerRow77_8Degree70Norm x).val+(boundaryFullPowerDegree70Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree70Norm x).property (boundaryFullPowerDegree70Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree70Norm,boundaryFullPowerDegree70Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))))))=(boundaryFullPowerDegree70Block5Norm x).val+(boundaryFullPowerDegree70Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block5Norm x).property (boundaryFullPowerDegree70Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block5Norm,boundaryFullPowerDegree70Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x))))))))=(boundaryFullPowerDegree70Block3Norm x).val+(boundaryFullPowerDegree70Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block3Norm x).property (boundaryFullPowerDegree70Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block3Norm,boundaryFullPowerDegree70Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x))=c} := by

  have he : ((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x))=(boundaryRePowerRow77_12Degree70Norm x).val+(boundaryRePowerRow77_13Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree70Norm x).property (boundaryRePowerRow77_13Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree70Norm,boundaryRePowerRow77_13Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x))))=(boundaryRePowerRow77_11Degree70Norm x).val+(boundaryFullPowerDegree70Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree70Norm x).property (boundaryFullPowerDegree70Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree70Norm,boundaryFullPowerDegree70Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x))=c} := by

  have he : ((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x))=(boundaryRePowerRow77_15Degree70Norm x).val+(boundaryRePowerRow77_16Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree70Norm x).property (boundaryRePowerRow77_16Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree70Norm,boundaryRePowerRow77_16Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x))))=(boundaryRePowerRow77_14Degree70Norm x).val+(boundaryFullPowerDegree70Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree70Norm x).property (boundaryFullPowerDegree70Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree70Norm,boundaryFullPowerDegree70Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x))))))=(boundaryFullPowerDegree70Block11Norm x).val+(boundaryFullPowerDegree70Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block11Norm x).property (boundaryFullPowerDegree70Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block11Norm,boundaryFullPowerDegree70Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x))=c} := by

  have he : ((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x))=(boundaryRePowerRow77_18Degree70Norm x).val+(boundaryRePowerRow77_19Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree70Norm x).property (boundaryRePowerRow77_19Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree70Norm,boundaryRePowerRow77_19Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x))))=(boundaryRePowerRow77_17Degree70Norm x).val+(boundaryFullPowerDegree70Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree70Norm x).property (boundaryFullPowerDegree70Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree70Norm,boundaryFullPowerDegree70Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))=c} := by

  have he : ((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))=(boundaryRePowerRow77_21Degree70Norm x).val+(boundaryRePowerRow77_22Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree70Norm x).property (boundaryRePowerRow77_22Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree70Norm,boundaryRePowerRow77_22Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))=(boundaryRePowerRow77_20Degree70Norm x).val+(boundaryFullPowerDegree70Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree70Norm x).property (boundaryFullPowerDegree70Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree70Norm,boundaryFullPowerDegree70Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))))=(boundaryFullPowerDegree70Block16Norm x).val+(boundaryFullPowerDegree70Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block16Norm x).property (boundaryFullPowerDegree70Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block16Norm,boundaryFullPowerDegree70Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))))))=(boundaryFullPowerDegree70Block14Norm x).val+(boundaryFullPowerDegree70Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block14Norm x).property (boundaryFullPowerDegree70Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block14Norm,boundaryFullPowerDegree70Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x)))))))))+(((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x)))))))))+(((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x))))))))))=(boundaryFullPowerDegree70Block9Norm x).val+(boundaryFullPowerDegree70Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block9Norm x).property (boundaryFullPowerDegree70Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block9Norm,boundaryFullPowerDegree70Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x))=c} := by

  have he : ((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x))=(boundaryImPowerRow77_0Degree70Norm x).val+(boundaryImPowerRow77_1Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree70Norm x).property (boundaryImPowerRow77_1Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree70Norm,boundaryImPowerRow77_1Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x))=c} := by

  have he : ((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x))=(boundaryImPowerRow77_3Degree70Norm x).val+(boundaryImPowerRow77_4Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree70Norm x).property (boundaryImPowerRow77_4Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree70Norm,boundaryImPowerRow77_4Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x))))=(boundaryImPowerRow77_2Degree70Norm x).val+(boundaryFullPowerDegree70Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree70Norm x).property (boundaryFullPowerDegree70Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree70Norm,boundaryFullPowerDegree70Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x))))))=(boundaryFullPowerDegree70Block22Norm x).val+(boundaryFullPowerDegree70Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block22Norm x).property (boundaryFullPowerDegree70Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block22Norm,boundaryFullPowerDegree70Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x))=c} := by

  have he : ((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x))=(boundaryImPowerRow77_6Degree70Norm x).val+(boundaryImPowerRow77_7Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree70Norm x).property (boundaryImPowerRow77_7Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree70Norm,boundaryImPowerRow77_7Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x))))=(boundaryImPowerRow77_5Degree70Norm x).val+(boundaryFullPowerDegree70Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree70Norm x).property (boundaryFullPowerDegree70Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree70Norm,boundaryFullPowerDegree70Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))=c} := by

  have he : ((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))=(boundaryImPowerRow77_9Degree70Norm x).val+(boundaryImPowerRow77_10Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree70Norm x).property (boundaryImPowerRow77_10Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree70Norm,boundaryImPowerRow77_10Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))))=(boundaryImPowerRow77_8Degree70Norm x).val+(boundaryFullPowerDegree70Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree70Norm x).property (boundaryFullPowerDegree70Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree70Norm,boundaryFullPowerDegree70Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))))))=(boundaryFullPowerDegree70Block27Norm x).val+(boundaryFullPowerDegree70Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block27Norm x).property (boundaryFullPowerDegree70Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block27Norm,boundaryFullPowerDegree70Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x))))))))=(boundaryFullPowerDegree70Block25Norm x).val+(boundaryFullPowerDegree70Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block25Norm x).property (boundaryFullPowerDegree70Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block25Norm,boundaryFullPowerDegree70Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x))=c} := by

  have he : ((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x))=(boundaryImPowerRow77_12Degree70Norm x).val+(boundaryImPowerRow77_13Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree70Norm x).property (boundaryImPowerRow77_13Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree70Norm,boundaryImPowerRow77_13Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x))))=(boundaryImPowerRow77_11Degree70Norm x).val+(boundaryFullPowerDegree70Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree70Norm x).property (boundaryFullPowerDegree70Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree70Norm,boundaryFullPowerDegree70Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x))=c} := by

  have he : ((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x))=(boundaryImPowerRow77_15Degree70Norm x).val+(boundaryImPowerRow77_16Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree70Norm x).property (boundaryImPowerRow77_16Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree70Norm,boundaryImPowerRow77_16Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x))))=(boundaryImPowerRow77_14Degree70Norm x).val+(boundaryFullPowerDegree70Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree70Norm x).property (boundaryFullPowerDegree70Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree70Norm,boundaryFullPowerDegree70Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x))))))=(boundaryFullPowerDegree70Block33Norm x).val+(boundaryFullPowerDegree70Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block33Norm x).property (boundaryFullPowerDegree70Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block33Norm,boundaryFullPowerDegree70Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x))=c} := by

  have he : ((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x))=(boundaryImPowerRow77_18Degree70Norm x).val+(boundaryImPowerRow77_19Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree70Norm x).property (boundaryImPowerRow77_19Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree70Norm,boundaryImPowerRow77_19Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x))))=(boundaryImPowerRow77_17Degree70Norm x).val+(boundaryFullPowerDegree70Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree70Norm x).property (boundaryFullPowerDegree70Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree70Norm,boundaryFullPowerDegree70Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))=c} := by

  have he : ((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))=(boundaryImPowerRow77_21Degree70Norm x).val+(boundaryLowPowerRow77Degree70Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree70Norm x).property (boundaryLowPowerRow77Degree70Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree70Norm,boundaryLowPowerRow77Degree70Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))=(boundaryImPowerRow77_20Degree70Norm x).val+(boundaryFullPowerDegree70Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree70Norm x).property (boundaryFullPowerDegree70Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree70Norm,boundaryFullPowerDegree70Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))=(boundaryFullPowerDegree70Block38Norm x).val+(boundaryFullPowerDegree70Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block38Norm x).property (boundaryFullPowerDegree70Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block38Norm,boundaryFullPowerDegree70Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))))=(boundaryFullPowerDegree70Block36Norm x).val+(boundaryFullPowerDegree70Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block36Norm x).property (boundaryFullPowerDegree70Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block36Norm,boundaryFullPowerDegree70Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x)))))))))+(((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x)))))))))+(((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))))))=(boundaryFullPowerDegree70Block31Norm x).val+(boundaryFullPowerDegree70Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block31Norm x).property (boundaryFullPowerDegree70Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block31Norm,boundaryFullPowerDegree70Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree70Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x)))))))))+(((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x)))))))))))+(((((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x)))))))))+(((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x)))))))))+(((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x)))))))))))+(((((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x)))))))))+(((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x))))))))))))=(boundaryFullPowerDegree70Block21Norm x).val+(boundaryFullPowerDegree70Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree70Block21Norm x).property (boundaryFullPowerDegree70Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block21Norm,boundaryFullPowerDegree70Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree70Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 70 x=c} := by

  have he0 : boundaryFullPowerRow77 70 x=((((((((((boundaryRePowerRow77_0 70 x)+(boundaryRePowerRow77_1 70 x)))+(((boundaryRePowerRow77_2 70 x)+(((boundaryRePowerRow77_3 70 x)+(boundaryRePowerRow77_4 70 x)))))))+(((((boundaryRePowerRow77_5 70 x)+(((boundaryRePowerRow77_6 70 x)+(boundaryRePowerRow77_7 70 x)))))+(((boundaryRePowerRow77_8 70 x)+(((boundaryRePowerRow77_9 70 x)+(boundaryRePowerRow77_10 70 x)))))))))+(((((((boundaryRePowerRow77_11 70 x)+(((boundaryRePowerRow77_12 70 x)+(boundaryRePowerRow77_13 70 x)))))+(((boundaryRePowerRow77_14 70 x)+(((boundaryRePowerRow77_15 70 x)+(boundaryRePowerRow77_16 70 x)))))))+(((((boundaryRePowerRow77_17 70 x)+(((boundaryRePowerRow77_18 70 x)+(boundaryRePowerRow77_19 70 x)))))+(((boundaryRePowerRow77_20 70 x)+(((boundaryRePowerRow77_21 70 x)+(boundaryRePowerRow77_22 70 x)))))))))))+(((((((((boundaryImPowerRow77_0 70 x)+(boundaryImPowerRow77_1 70 x)))+(((boundaryImPowerRow77_2 70 x)+(((boundaryImPowerRow77_3 70 x)+(boundaryImPowerRow77_4 70 x)))))))+(((((boundaryImPowerRow77_5 70 x)+(((boundaryImPowerRow77_6 70 x)+(boundaryImPowerRow77_7 70 x)))))+(((boundaryImPowerRow77_8 70 x)+(((boundaryImPowerRow77_9 70 x)+(boundaryImPowerRow77_10 70 x)))))))))+(((((((boundaryImPowerRow77_11 70 x)+(((boundaryImPowerRow77_12 70 x)+(boundaryImPowerRow77_13 70 x)))))+(((boundaryImPowerRow77_14 70 x)+(((boundaryImPowerRow77_15 70 x)+(boundaryImPowerRow77_16 70 x)))))))+(((((boundaryImPowerRow77_17 70 x)+(((boundaryImPowerRow77_18 70 x)+(boundaryImPowerRow77_19 70 x)))))+(((boundaryImPowerRow77_20 70 x)+(((boundaryImPowerRow77_21 70 x)+(boundaryLowPowerRow77 70 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree70Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree70Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
