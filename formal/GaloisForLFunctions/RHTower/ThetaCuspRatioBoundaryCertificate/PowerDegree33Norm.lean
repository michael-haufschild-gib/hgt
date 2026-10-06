import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree33Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree33Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x))=c} := by

  have he : ((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x))=(boundaryRePowerRow77_0Degree33Norm x).val+(boundaryRePowerRow77_1Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree33Norm x).property (boundaryRePowerRow77_1Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree33Norm,boundaryRePowerRow77_1Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x))=c} := by

  have he : ((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x))=(boundaryRePowerRow77_3Degree33Norm x).val+(boundaryRePowerRow77_4Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree33Norm x).property (boundaryRePowerRow77_4Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree33Norm,boundaryRePowerRow77_4Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x))))=(boundaryRePowerRow77_2Degree33Norm x).val+(boundaryFullPowerDegree33Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree33Norm x).property (boundaryFullPowerDegree33Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree33Norm,boundaryFullPowerDegree33Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x))))))=(boundaryFullPowerDegree33Block0Norm x).val+(boundaryFullPowerDegree33Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block0Norm x).property (boundaryFullPowerDegree33Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block0Norm,boundaryFullPowerDegree33Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x))=c} := by

  have he : ((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x))=(boundaryRePowerRow77_6Degree33Norm x).val+(boundaryRePowerRow77_7Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree33Norm x).property (boundaryRePowerRow77_7Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree33Norm,boundaryRePowerRow77_7Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x))))=(boundaryRePowerRow77_5Degree33Norm x).val+(boundaryFullPowerDegree33Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree33Norm x).property (boundaryFullPowerDegree33Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree33Norm,boundaryFullPowerDegree33Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))=c} := by

  have he : ((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))=(boundaryRePowerRow77_9Degree33Norm x).val+(boundaryRePowerRow77_10Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree33Norm x).property (boundaryRePowerRow77_10Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree33Norm,boundaryRePowerRow77_10Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))))=(boundaryRePowerRow77_8Degree33Norm x).val+(boundaryFullPowerDegree33Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree33Norm x).property (boundaryFullPowerDegree33Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree33Norm,boundaryFullPowerDegree33Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))))))=(boundaryFullPowerDegree33Block5Norm x).val+(boundaryFullPowerDegree33Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block5Norm x).property (boundaryFullPowerDegree33Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block5Norm,boundaryFullPowerDegree33Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x))))))))=(boundaryFullPowerDegree33Block3Norm x).val+(boundaryFullPowerDegree33Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block3Norm x).property (boundaryFullPowerDegree33Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block3Norm,boundaryFullPowerDegree33Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x))=c} := by

  have he : ((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x))=(boundaryRePowerRow77_12Degree33Norm x).val+(boundaryRePowerRow77_13Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree33Norm x).property (boundaryRePowerRow77_13Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree33Norm,boundaryRePowerRow77_13Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x))))=(boundaryRePowerRow77_11Degree33Norm x).val+(boundaryFullPowerDegree33Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree33Norm x).property (boundaryFullPowerDegree33Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree33Norm,boundaryFullPowerDegree33Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x))=c} := by

  have he : ((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x))=(boundaryRePowerRow77_15Degree33Norm x).val+(boundaryRePowerRow77_16Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree33Norm x).property (boundaryRePowerRow77_16Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree33Norm,boundaryRePowerRow77_16Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x))))=(boundaryRePowerRow77_14Degree33Norm x).val+(boundaryFullPowerDegree33Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree33Norm x).property (boundaryFullPowerDegree33Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree33Norm,boundaryFullPowerDegree33Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x))))))=(boundaryFullPowerDegree33Block11Norm x).val+(boundaryFullPowerDegree33Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block11Norm x).property (boundaryFullPowerDegree33Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block11Norm,boundaryFullPowerDegree33Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x))=c} := by

  have he : ((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x))=(boundaryRePowerRow77_18Degree33Norm x).val+(boundaryRePowerRow77_19Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree33Norm x).property (boundaryRePowerRow77_19Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree33Norm,boundaryRePowerRow77_19Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x))))=(boundaryRePowerRow77_17Degree33Norm x).val+(boundaryFullPowerDegree33Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree33Norm x).property (boundaryFullPowerDegree33Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree33Norm,boundaryFullPowerDegree33Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))=c} := by

  have he : ((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))=(boundaryRePowerRow77_21Degree33Norm x).val+(boundaryRePowerRow77_22Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree33Norm x).property (boundaryRePowerRow77_22Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree33Norm,boundaryRePowerRow77_22Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))=(boundaryRePowerRow77_20Degree33Norm x).val+(boundaryFullPowerDegree33Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree33Norm x).property (boundaryFullPowerDegree33Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree33Norm,boundaryFullPowerDegree33Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))))=(boundaryFullPowerDegree33Block16Norm x).val+(boundaryFullPowerDegree33Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block16Norm x).property (boundaryFullPowerDegree33Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block16Norm,boundaryFullPowerDegree33Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))))))=(boundaryFullPowerDegree33Block14Norm x).val+(boundaryFullPowerDegree33Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block14Norm x).property (boundaryFullPowerDegree33Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block14Norm,boundaryFullPowerDegree33Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x)))))))))+(((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x)))))))))+(((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x))))))))))=(boundaryFullPowerDegree33Block9Norm x).val+(boundaryFullPowerDegree33Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block9Norm x).property (boundaryFullPowerDegree33Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block9Norm,boundaryFullPowerDegree33Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x))=c} := by

  have he : ((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x))=(boundaryImPowerRow77_0Degree33Norm x).val+(boundaryImPowerRow77_1Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree33Norm x).property (boundaryImPowerRow77_1Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree33Norm,boundaryImPowerRow77_1Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x))=c} := by

  have he : ((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x))=(boundaryImPowerRow77_3Degree33Norm x).val+(boundaryImPowerRow77_4Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree33Norm x).property (boundaryImPowerRow77_4Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree33Norm,boundaryImPowerRow77_4Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x))))=(boundaryImPowerRow77_2Degree33Norm x).val+(boundaryFullPowerDegree33Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree33Norm x).property (boundaryFullPowerDegree33Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree33Norm,boundaryFullPowerDegree33Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x))))))=(boundaryFullPowerDegree33Block22Norm x).val+(boundaryFullPowerDegree33Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block22Norm x).property (boundaryFullPowerDegree33Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block22Norm,boundaryFullPowerDegree33Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x))=c} := by

  have he : ((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x))=(boundaryImPowerRow77_6Degree33Norm x).val+(boundaryImPowerRow77_7Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree33Norm x).property (boundaryImPowerRow77_7Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree33Norm,boundaryImPowerRow77_7Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x))))=(boundaryImPowerRow77_5Degree33Norm x).val+(boundaryFullPowerDegree33Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree33Norm x).property (boundaryFullPowerDegree33Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree33Norm,boundaryFullPowerDegree33Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))=c} := by

  have he : ((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))=(boundaryImPowerRow77_9Degree33Norm x).val+(boundaryImPowerRow77_10Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree33Norm x).property (boundaryImPowerRow77_10Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree33Norm,boundaryImPowerRow77_10Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))))=(boundaryImPowerRow77_8Degree33Norm x).val+(boundaryFullPowerDegree33Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree33Norm x).property (boundaryFullPowerDegree33Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree33Norm,boundaryFullPowerDegree33Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))))))=(boundaryFullPowerDegree33Block27Norm x).val+(boundaryFullPowerDegree33Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block27Norm x).property (boundaryFullPowerDegree33Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block27Norm,boundaryFullPowerDegree33Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x))))))))=(boundaryFullPowerDegree33Block25Norm x).val+(boundaryFullPowerDegree33Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block25Norm x).property (boundaryFullPowerDegree33Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block25Norm,boundaryFullPowerDegree33Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x))=c} := by

  have he : ((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x))=(boundaryImPowerRow77_12Degree33Norm x).val+(boundaryImPowerRow77_13Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree33Norm x).property (boundaryImPowerRow77_13Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree33Norm,boundaryImPowerRow77_13Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x))))=(boundaryImPowerRow77_11Degree33Norm x).val+(boundaryFullPowerDegree33Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree33Norm x).property (boundaryFullPowerDegree33Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree33Norm,boundaryFullPowerDegree33Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x))=c} := by

  have he : ((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x))=(boundaryImPowerRow77_15Degree33Norm x).val+(boundaryImPowerRow77_16Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree33Norm x).property (boundaryImPowerRow77_16Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree33Norm,boundaryImPowerRow77_16Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x))))=(boundaryImPowerRow77_14Degree33Norm x).val+(boundaryFullPowerDegree33Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree33Norm x).property (boundaryFullPowerDegree33Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree33Norm,boundaryFullPowerDegree33Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x))))))=(boundaryFullPowerDegree33Block33Norm x).val+(boundaryFullPowerDegree33Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block33Norm x).property (boundaryFullPowerDegree33Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block33Norm,boundaryFullPowerDegree33Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x))=c} := by

  have he : ((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x))=(boundaryImPowerRow77_18Degree33Norm x).val+(boundaryImPowerRow77_19Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree33Norm x).property (boundaryImPowerRow77_19Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree33Norm,boundaryImPowerRow77_19Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x))))=(boundaryImPowerRow77_17Degree33Norm x).val+(boundaryFullPowerDegree33Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree33Norm x).property (boundaryFullPowerDegree33Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree33Norm,boundaryFullPowerDegree33Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))=c} := by

  have he : ((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))=(boundaryImPowerRow77_21Degree33Norm x).val+(boundaryLowPowerRow77Degree33Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree33Norm x).property (boundaryLowPowerRow77Degree33Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree33Norm,boundaryLowPowerRow77Degree33Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))=(boundaryImPowerRow77_20Degree33Norm x).val+(boundaryFullPowerDegree33Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree33Norm x).property (boundaryFullPowerDegree33Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree33Norm,boundaryFullPowerDegree33Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))=(boundaryFullPowerDegree33Block38Norm x).val+(boundaryFullPowerDegree33Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block38Norm x).property (boundaryFullPowerDegree33Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block38Norm,boundaryFullPowerDegree33Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))))=(boundaryFullPowerDegree33Block36Norm x).val+(boundaryFullPowerDegree33Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block36Norm x).property (boundaryFullPowerDegree33Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block36Norm,boundaryFullPowerDegree33Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x)))))))))+(((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x)))))))))+(((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))))))=(boundaryFullPowerDegree33Block31Norm x).val+(boundaryFullPowerDegree33Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block31Norm x).property (boundaryFullPowerDegree33Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block31Norm,boundaryFullPowerDegree33Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree33Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x)))))))))+(((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x)))))))))))+(((((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x)))))))))+(((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x)))))))))+(((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x)))))))))))+(((((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x)))))))))+(((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x))))))))))))=(boundaryFullPowerDegree33Block21Norm x).val+(boundaryFullPowerDegree33Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree33Block21Norm x).property (boundaryFullPowerDegree33Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block21Norm,boundaryFullPowerDegree33Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree33Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 33 x=c} := by

  have he0 : boundaryFullPowerRow77 33 x=((((((((((boundaryRePowerRow77_0 33 x)+(boundaryRePowerRow77_1 33 x)))+(((boundaryRePowerRow77_2 33 x)+(((boundaryRePowerRow77_3 33 x)+(boundaryRePowerRow77_4 33 x)))))))+(((((boundaryRePowerRow77_5 33 x)+(((boundaryRePowerRow77_6 33 x)+(boundaryRePowerRow77_7 33 x)))))+(((boundaryRePowerRow77_8 33 x)+(((boundaryRePowerRow77_9 33 x)+(boundaryRePowerRow77_10 33 x)))))))))+(((((((boundaryRePowerRow77_11 33 x)+(((boundaryRePowerRow77_12 33 x)+(boundaryRePowerRow77_13 33 x)))))+(((boundaryRePowerRow77_14 33 x)+(((boundaryRePowerRow77_15 33 x)+(boundaryRePowerRow77_16 33 x)))))))+(((((boundaryRePowerRow77_17 33 x)+(((boundaryRePowerRow77_18 33 x)+(boundaryRePowerRow77_19 33 x)))))+(((boundaryRePowerRow77_20 33 x)+(((boundaryRePowerRow77_21 33 x)+(boundaryRePowerRow77_22 33 x)))))))))))+(((((((((boundaryImPowerRow77_0 33 x)+(boundaryImPowerRow77_1 33 x)))+(((boundaryImPowerRow77_2 33 x)+(((boundaryImPowerRow77_3 33 x)+(boundaryImPowerRow77_4 33 x)))))))+(((((boundaryImPowerRow77_5 33 x)+(((boundaryImPowerRow77_6 33 x)+(boundaryImPowerRow77_7 33 x)))))+(((boundaryImPowerRow77_8 33 x)+(((boundaryImPowerRow77_9 33 x)+(boundaryImPowerRow77_10 33 x)))))))))+(((((((boundaryImPowerRow77_11 33 x)+(((boundaryImPowerRow77_12 33 x)+(boundaryImPowerRow77_13 33 x)))))+(((boundaryImPowerRow77_14 33 x)+(((boundaryImPowerRow77_15 33 x)+(boundaryImPowerRow77_16 33 x)))))))+(((((boundaryImPowerRow77_17 33 x)+(((boundaryImPowerRow77_18 33 x)+(boundaryImPowerRow77_19 33 x)))))+(((boundaryImPowerRow77_20 33 x)+(((boundaryImPowerRow77_21 33 x)+(boundaryLowPowerRow77 33 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree33Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree33Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
