import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree77Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree77Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x))=c} := by

  have he : ((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x))=(boundaryRePowerRow77_0Degree77Norm x).val+(boundaryRePowerRow77_1Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree77Norm x).property (boundaryRePowerRow77_1Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree77Norm,boundaryRePowerRow77_1Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x))=c} := by

  have he : ((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x))=(boundaryRePowerRow77_3Degree77Norm x).val+(boundaryRePowerRow77_4Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree77Norm x).property (boundaryRePowerRow77_4Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree77Norm,boundaryRePowerRow77_4Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x))))=(boundaryRePowerRow77_2Degree77Norm x).val+(boundaryFullPowerDegree77Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree77Norm x).property (boundaryFullPowerDegree77Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree77Norm,boundaryFullPowerDegree77Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x))))))=(boundaryFullPowerDegree77Block0Norm x).val+(boundaryFullPowerDegree77Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block0Norm x).property (boundaryFullPowerDegree77Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block0Norm,boundaryFullPowerDegree77Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x))=c} := by

  have he : ((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x))=(boundaryRePowerRow77_6Degree77Norm x).val+(boundaryRePowerRow77_7Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree77Norm x).property (boundaryRePowerRow77_7Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree77Norm,boundaryRePowerRow77_7Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x))))=(boundaryRePowerRow77_5Degree77Norm x).val+(boundaryFullPowerDegree77Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree77Norm x).property (boundaryFullPowerDegree77Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree77Norm,boundaryFullPowerDegree77Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))=c} := by

  have he : ((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))=(boundaryRePowerRow77_9Degree77Norm x).val+(boundaryRePowerRow77_10Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree77Norm x).property (boundaryRePowerRow77_10Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree77Norm,boundaryRePowerRow77_10Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))))=(boundaryRePowerRow77_8Degree77Norm x).val+(boundaryFullPowerDegree77Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree77Norm x).property (boundaryFullPowerDegree77Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree77Norm,boundaryFullPowerDegree77Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))))))=(boundaryFullPowerDegree77Block5Norm x).val+(boundaryFullPowerDegree77Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block5Norm x).property (boundaryFullPowerDegree77Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block5Norm,boundaryFullPowerDegree77Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x))))))))=(boundaryFullPowerDegree77Block3Norm x).val+(boundaryFullPowerDegree77Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block3Norm x).property (boundaryFullPowerDegree77Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block3Norm,boundaryFullPowerDegree77Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x))=c} := by

  have he : ((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x))=(boundaryRePowerRow77_12Degree77Norm x).val+(boundaryRePowerRow77_13Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree77Norm x).property (boundaryRePowerRow77_13Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree77Norm,boundaryRePowerRow77_13Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x))))=(boundaryRePowerRow77_11Degree77Norm x).val+(boundaryFullPowerDegree77Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree77Norm x).property (boundaryFullPowerDegree77Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree77Norm,boundaryFullPowerDegree77Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x))=c} := by

  have he : ((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x))=(boundaryRePowerRow77_15Degree77Norm x).val+(boundaryRePowerRow77_16Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree77Norm x).property (boundaryRePowerRow77_16Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree77Norm,boundaryRePowerRow77_16Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x))))=(boundaryRePowerRow77_14Degree77Norm x).val+(boundaryFullPowerDegree77Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree77Norm x).property (boundaryFullPowerDegree77Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree77Norm,boundaryFullPowerDegree77Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x))))))=(boundaryFullPowerDegree77Block11Norm x).val+(boundaryFullPowerDegree77Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block11Norm x).property (boundaryFullPowerDegree77Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block11Norm,boundaryFullPowerDegree77Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x))=c} := by

  have he : ((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x))=(boundaryRePowerRow77_18Degree77Norm x).val+(boundaryRePowerRow77_19Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree77Norm x).property (boundaryRePowerRow77_19Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree77Norm,boundaryRePowerRow77_19Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x))))=(boundaryRePowerRow77_17Degree77Norm x).val+(boundaryFullPowerDegree77Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree77Norm x).property (boundaryFullPowerDegree77Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree77Norm,boundaryFullPowerDegree77Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))=c} := by

  have he : ((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))=(boundaryRePowerRow77_21Degree77Norm x).val+(boundaryRePowerRow77_22Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree77Norm x).property (boundaryRePowerRow77_22Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree77Norm,boundaryRePowerRow77_22Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))=(boundaryRePowerRow77_20Degree77Norm x).val+(boundaryFullPowerDegree77Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree77Norm x).property (boundaryFullPowerDegree77Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree77Norm,boundaryFullPowerDegree77Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))))=(boundaryFullPowerDegree77Block16Norm x).val+(boundaryFullPowerDegree77Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block16Norm x).property (boundaryFullPowerDegree77Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block16Norm,boundaryFullPowerDegree77Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))))))=(boundaryFullPowerDegree77Block14Norm x).val+(boundaryFullPowerDegree77Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block14Norm x).property (boundaryFullPowerDegree77Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block14Norm,boundaryFullPowerDegree77Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x)))))))))+(((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x)))))))))+(((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x))))))))))=(boundaryFullPowerDegree77Block9Norm x).val+(boundaryFullPowerDegree77Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block9Norm x).property (boundaryFullPowerDegree77Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block9Norm,boundaryFullPowerDegree77Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x))=c} := by

  have he : ((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x))=(boundaryImPowerRow77_0Degree77Norm x).val+(boundaryImPowerRow77_1Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree77Norm x).property (boundaryImPowerRow77_1Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree77Norm,boundaryImPowerRow77_1Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x))=c} := by

  have he : ((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x))=(boundaryImPowerRow77_3Degree77Norm x).val+(boundaryImPowerRow77_4Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree77Norm x).property (boundaryImPowerRow77_4Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree77Norm,boundaryImPowerRow77_4Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x))))=(boundaryImPowerRow77_2Degree77Norm x).val+(boundaryFullPowerDegree77Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree77Norm x).property (boundaryFullPowerDegree77Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree77Norm,boundaryFullPowerDegree77Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x))))))=(boundaryFullPowerDegree77Block22Norm x).val+(boundaryFullPowerDegree77Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block22Norm x).property (boundaryFullPowerDegree77Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block22Norm,boundaryFullPowerDegree77Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x))=c} := by

  have he : ((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x))=(boundaryImPowerRow77_6Degree77Norm x).val+(boundaryImPowerRow77_7Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree77Norm x).property (boundaryImPowerRow77_7Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree77Norm,boundaryImPowerRow77_7Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x))))=(boundaryImPowerRow77_5Degree77Norm x).val+(boundaryFullPowerDegree77Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree77Norm x).property (boundaryFullPowerDegree77Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree77Norm,boundaryFullPowerDegree77Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))=c} := by

  have he : ((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))=(boundaryImPowerRow77_9Degree77Norm x).val+(boundaryImPowerRow77_10Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree77Norm x).property (boundaryImPowerRow77_10Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree77Norm,boundaryImPowerRow77_10Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))))=(boundaryImPowerRow77_8Degree77Norm x).val+(boundaryFullPowerDegree77Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree77Norm x).property (boundaryFullPowerDegree77Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree77Norm,boundaryFullPowerDegree77Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))))))=(boundaryFullPowerDegree77Block27Norm x).val+(boundaryFullPowerDegree77Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block27Norm x).property (boundaryFullPowerDegree77Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block27Norm,boundaryFullPowerDegree77Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x))))))))=(boundaryFullPowerDegree77Block25Norm x).val+(boundaryFullPowerDegree77Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block25Norm x).property (boundaryFullPowerDegree77Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block25Norm,boundaryFullPowerDegree77Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x))=c} := by

  have he : ((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x))=(boundaryImPowerRow77_12Degree77Norm x).val+(boundaryImPowerRow77_13Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree77Norm x).property (boundaryImPowerRow77_13Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree77Norm,boundaryImPowerRow77_13Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x))))=(boundaryImPowerRow77_11Degree77Norm x).val+(boundaryFullPowerDegree77Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree77Norm x).property (boundaryFullPowerDegree77Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree77Norm,boundaryFullPowerDegree77Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x))=c} := by

  have he : ((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x))=(boundaryImPowerRow77_15Degree77Norm x).val+(boundaryImPowerRow77_16Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree77Norm x).property (boundaryImPowerRow77_16Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree77Norm,boundaryImPowerRow77_16Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x))))=(boundaryImPowerRow77_14Degree77Norm x).val+(boundaryFullPowerDegree77Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree77Norm x).property (boundaryFullPowerDegree77Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree77Norm,boundaryFullPowerDegree77Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x))))))=(boundaryFullPowerDegree77Block33Norm x).val+(boundaryFullPowerDegree77Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block33Norm x).property (boundaryFullPowerDegree77Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block33Norm,boundaryFullPowerDegree77Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x))=c} := by

  have he : ((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x))=(boundaryImPowerRow77_18Degree77Norm x).val+(boundaryImPowerRow77_19Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree77Norm x).property (boundaryImPowerRow77_19Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree77Norm,boundaryImPowerRow77_19Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x))))=(boundaryImPowerRow77_17Degree77Norm x).val+(boundaryFullPowerDegree77Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree77Norm x).property (boundaryFullPowerDegree77Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree77Norm,boundaryFullPowerDegree77Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))=c} := by

  have he : ((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))=(boundaryImPowerRow77_21Degree77Norm x).val+(boundaryLowPowerRow77Degree77Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree77Norm x).property (boundaryLowPowerRow77Degree77Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree77Norm,boundaryLowPowerRow77Degree77Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))=(boundaryImPowerRow77_20Degree77Norm x).val+(boundaryFullPowerDegree77Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree77Norm x).property (boundaryFullPowerDegree77Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree77Norm,boundaryFullPowerDegree77Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))=(boundaryFullPowerDegree77Block38Norm x).val+(boundaryFullPowerDegree77Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block38Norm x).property (boundaryFullPowerDegree77Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block38Norm,boundaryFullPowerDegree77Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))))=(boundaryFullPowerDegree77Block36Norm x).val+(boundaryFullPowerDegree77Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block36Norm x).property (boundaryFullPowerDegree77Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block36Norm,boundaryFullPowerDegree77Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x)))))))))+(((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x)))))))))+(((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))))))=(boundaryFullPowerDegree77Block31Norm x).val+(boundaryFullPowerDegree77Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block31Norm x).property (boundaryFullPowerDegree77Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block31Norm,boundaryFullPowerDegree77Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree77Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x)))))))))+(((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x)))))))))))+(((((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x)))))))))+(((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x)))))))))+(((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x)))))))))))+(((((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x)))))))))+(((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x))))))))))))=(boundaryFullPowerDegree77Block21Norm x).val+(boundaryFullPowerDegree77Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree77Block21Norm x).property (boundaryFullPowerDegree77Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block21Norm,boundaryFullPowerDegree77Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree77Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 77 x=c} := by

  have he0 : boundaryFullPowerRow77 77 x=((((((((((boundaryRePowerRow77_0 77 x)+(boundaryRePowerRow77_1 77 x)))+(((boundaryRePowerRow77_2 77 x)+(((boundaryRePowerRow77_3 77 x)+(boundaryRePowerRow77_4 77 x)))))))+(((((boundaryRePowerRow77_5 77 x)+(((boundaryRePowerRow77_6 77 x)+(boundaryRePowerRow77_7 77 x)))))+(((boundaryRePowerRow77_8 77 x)+(((boundaryRePowerRow77_9 77 x)+(boundaryRePowerRow77_10 77 x)))))))))+(((((((boundaryRePowerRow77_11 77 x)+(((boundaryRePowerRow77_12 77 x)+(boundaryRePowerRow77_13 77 x)))))+(((boundaryRePowerRow77_14 77 x)+(((boundaryRePowerRow77_15 77 x)+(boundaryRePowerRow77_16 77 x)))))))+(((((boundaryRePowerRow77_17 77 x)+(((boundaryRePowerRow77_18 77 x)+(boundaryRePowerRow77_19 77 x)))))+(((boundaryRePowerRow77_20 77 x)+(((boundaryRePowerRow77_21 77 x)+(boundaryRePowerRow77_22 77 x)))))))))))+(((((((((boundaryImPowerRow77_0 77 x)+(boundaryImPowerRow77_1 77 x)))+(((boundaryImPowerRow77_2 77 x)+(((boundaryImPowerRow77_3 77 x)+(boundaryImPowerRow77_4 77 x)))))))+(((((boundaryImPowerRow77_5 77 x)+(((boundaryImPowerRow77_6 77 x)+(boundaryImPowerRow77_7 77 x)))))+(((boundaryImPowerRow77_8 77 x)+(((boundaryImPowerRow77_9 77 x)+(boundaryImPowerRow77_10 77 x)))))))))+(((((((boundaryImPowerRow77_11 77 x)+(((boundaryImPowerRow77_12 77 x)+(boundaryImPowerRow77_13 77 x)))))+(((boundaryImPowerRow77_14 77 x)+(((boundaryImPowerRow77_15 77 x)+(boundaryImPowerRow77_16 77 x)))))))+(((((boundaryImPowerRow77_17 77 x)+(((boundaryImPowerRow77_18 77 x)+(boundaryImPowerRow77_19 77 x)))))+(((boundaryImPowerRow77_20 77 x)+(((boundaryImPowerRow77_21 77 x)+(boundaryLowPowerRow77 77 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree77Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree77Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
