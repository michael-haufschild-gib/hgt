import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree30Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree30Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x))=c} := by

  have he : ((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x))=(boundaryRePowerRow77_0Degree30Norm x).val+(boundaryRePowerRow77_1Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree30Norm x).property (boundaryRePowerRow77_1Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree30Norm,boundaryRePowerRow77_1Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x))=c} := by

  have he : ((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x))=(boundaryRePowerRow77_3Degree30Norm x).val+(boundaryRePowerRow77_4Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree30Norm x).property (boundaryRePowerRow77_4Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree30Norm,boundaryRePowerRow77_4Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x))))=(boundaryRePowerRow77_2Degree30Norm x).val+(boundaryFullPowerDegree30Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree30Norm x).property (boundaryFullPowerDegree30Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree30Norm,boundaryFullPowerDegree30Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x))))))=(boundaryFullPowerDegree30Block0Norm x).val+(boundaryFullPowerDegree30Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block0Norm x).property (boundaryFullPowerDegree30Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block0Norm,boundaryFullPowerDegree30Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x))=c} := by

  have he : ((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x))=(boundaryRePowerRow77_6Degree30Norm x).val+(boundaryRePowerRow77_7Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree30Norm x).property (boundaryRePowerRow77_7Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree30Norm,boundaryRePowerRow77_7Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x))))=(boundaryRePowerRow77_5Degree30Norm x).val+(boundaryFullPowerDegree30Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree30Norm x).property (boundaryFullPowerDegree30Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree30Norm,boundaryFullPowerDegree30Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))=c} := by

  have he : ((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))=(boundaryRePowerRow77_9Degree30Norm x).val+(boundaryRePowerRow77_10Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree30Norm x).property (boundaryRePowerRow77_10Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree30Norm,boundaryRePowerRow77_10Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))))=(boundaryRePowerRow77_8Degree30Norm x).val+(boundaryFullPowerDegree30Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree30Norm x).property (boundaryFullPowerDegree30Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree30Norm,boundaryFullPowerDegree30Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))))))=(boundaryFullPowerDegree30Block5Norm x).val+(boundaryFullPowerDegree30Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block5Norm x).property (boundaryFullPowerDegree30Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block5Norm,boundaryFullPowerDegree30Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x))))))))=(boundaryFullPowerDegree30Block3Norm x).val+(boundaryFullPowerDegree30Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block3Norm x).property (boundaryFullPowerDegree30Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block3Norm,boundaryFullPowerDegree30Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x))=c} := by

  have he : ((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x))=(boundaryRePowerRow77_12Degree30Norm x).val+(boundaryRePowerRow77_13Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree30Norm x).property (boundaryRePowerRow77_13Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree30Norm,boundaryRePowerRow77_13Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x))))=(boundaryRePowerRow77_11Degree30Norm x).val+(boundaryFullPowerDegree30Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree30Norm x).property (boundaryFullPowerDegree30Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree30Norm,boundaryFullPowerDegree30Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x))=c} := by

  have he : ((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x))=(boundaryRePowerRow77_15Degree30Norm x).val+(boundaryRePowerRow77_16Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree30Norm x).property (boundaryRePowerRow77_16Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree30Norm,boundaryRePowerRow77_16Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x))))=(boundaryRePowerRow77_14Degree30Norm x).val+(boundaryFullPowerDegree30Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree30Norm x).property (boundaryFullPowerDegree30Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree30Norm,boundaryFullPowerDegree30Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x))))))=(boundaryFullPowerDegree30Block11Norm x).val+(boundaryFullPowerDegree30Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block11Norm x).property (boundaryFullPowerDegree30Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block11Norm,boundaryFullPowerDegree30Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x))=c} := by

  have he : ((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x))=(boundaryRePowerRow77_18Degree30Norm x).val+(boundaryRePowerRow77_19Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree30Norm x).property (boundaryRePowerRow77_19Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree30Norm,boundaryRePowerRow77_19Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x))))=(boundaryRePowerRow77_17Degree30Norm x).val+(boundaryFullPowerDegree30Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree30Norm x).property (boundaryFullPowerDegree30Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree30Norm,boundaryFullPowerDegree30Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))=c} := by

  have he : ((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))=(boundaryRePowerRow77_21Degree30Norm x).val+(boundaryRePowerRow77_22Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree30Norm x).property (boundaryRePowerRow77_22Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree30Norm,boundaryRePowerRow77_22Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))=(boundaryRePowerRow77_20Degree30Norm x).val+(boundaryFullPowerDegree30Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree30Norm x).property (boundaryFullPowerDegree30Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree30Norm,boundaryFullPowerDegree30Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))))=(boundaryFullPowerDegree30Block16Norm x).val+(boundaryFullPowerDegree30Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block16Norm x).property (boundaryFullPowerDegree30Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block16Norm,boundaryFullPowerDegree30Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))))))=(boundaryFullPowerDegree30Block14Norm x).val+(boundaryFullPowerDegree30Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block14Norm x).property (boundaryFullPowerDegree30Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block14Norm,boundaryFullPowerDegree30Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x)))))))))+(((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x)))))))))+(((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x))))))))))=(boundaryFullPowerDegree30Block9Norm x).val+(boundaryFullPowerDegree30Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block9Norm x).property (boundaryFullPowerDegree30Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block9Norm,boundaryFullPowerDegree30Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x))=c} := by

  have he : ((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x))=(boundaryImPowerRow77_0Degree30Norm x).val+(boundaryImPowerRow77_1Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree30Norm x).property (boundaryImPowerRow77_1Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree30Norm,boundaryImPowerRow77_1Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x))=c} := by

  have he : ((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x))=(boundaryImPowerRow77_3Degree30Norm x).val+(boundaryImPowerRow77_4Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree30Norm x).property (boundaryImPowerRow77_4Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree30Norm,boundaryImPowerRow77_4Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x))))=(boundaryImPowerRow77_2Degree30Norm x).val+(boundaryFullPowerDegree30Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree30Norm x).property (boundaryFullPowerDegree30Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree30Norm,boundaryFullPowerDegree30Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x))))))=(boundaryFullPowerDegree30Block22Norm x).val+(boundaryFullPowerDegree30Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block22Norm x).property (boundaryFullPowerDegree30Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block22Norm,boundaryFullPowerDegree30Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x))=c} := by

  have he : ((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x))=(boundaryImPowerRow77_6Degree30Norm x).val+(boundaryImPowerRow77_7Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree30Norm x).property (boundaryImPowerRow77_7Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree30Norm,boundaryImPowerRow77_7Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x))))=(boundaryImPowerRow77_5Degree30Norm x).val+(boundaryFullPowerDegree30Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree30Norm x).property (boundaryFullPowerDegree30Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree30Norm,boundaryFullPowerDegree30Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))=c} := by

  have he : ((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))=(boundaryImPowerRow77_9Degree30Norm x).val+(boundaryImPowerRow77_10Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree30Norm x).property (boundaryImPowerRow77_10Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree30Norm,boundaryImPowerRow77_10Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))))=(boundaryImPowerRow77_8Degree30Norm x).val+(boundaryFullPowerDegree30Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree30Norm x).property (boundaryFullPowerDegree30Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree30Norm,boundaryFullPowerDegree30Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))))))=(boundaryFullPowerDegree30Block27Norm x).val+(boundaryFullPowerDegree30Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block27Norm x).property (boundaryFullPowerDegree30Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block27Norm,boundaryFullPowerDegree30Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x))))))))=(boundaryFullPowerDegree30Block25Norm x).val+(boundaryFullPowerDegree30Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block25Norm x).property (boundaryFullPowerDegree30Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block25Norm,boundaryFullPowerDegree30Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x))=c} := by

  have he : ((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x))=(boundaryImPowerRow77_12Degree30Norm x).val+(boundaryImPowerRow77_13Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree30Norm x).property (boundaryImPowerRow77_13Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree30Norm,boundaryImPowerRow77_13Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x))))=(boundaryImPowerRow77_11Degree30Norm x).val+(boundaryFullPowerDegree30Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree30Norm x).property (boundaryFullPowerDegree30Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree30Norm,boundaryFullPowerDegree30Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x))=c} := by

  have he : ((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x))=(boundaryImPowerRow77_15Degree30Norm x).val+(boundaryImPowerRow77_16Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree30Norm x).property (boundaryImPowerRow77_16Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree30Norm,boundaryImPowerRow77_16Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x))))=(boundaryImPowerRow77_14Degree30Norm x).val+(boundaryFullPowerDegree30Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree30Norm x).property (boundaryFullPowerDegree30Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree30Norm,boundaryFullPowerDegree30Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x))))))=(boundaryFullPowerDegree30Block33Norm x).val+(boundaryFullPowerDegree30Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block33Norm x).property (boundaryFullPowerDegree30Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block33Norm,boundaryFullPowerDegree30Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x))=c} := by

  have he : ((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x))=(boundaryImPowerRow77_18Degree30Norm x).val+(boundaryImPowerRow77_19Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree30Norm x).property (boundaryImPowerRow77_19Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree30Norm,boundaryImPowerRow77_19Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x))))=(boundaryImPowerRow77_17Degree30Norm x).val+(boundaryFullPowerDegree30Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree30Norm x).property (boundaryFullPowerDegree30Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree30Norm,boundaryFullPowerDegree30Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))=c} := by

  have he : ((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))=(boundaryImPowerRow77_21Degree30Norm x).val+(boundaryLowPowerRow77Degree30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree30Norm x).property (boundaryLowPowerRow77Degree30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree30Norm,boundaryLowPowerRow77Degree30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))=(boundaryImPowerRow77_20Degree30Norm x).val+(boundaryFullPowerDegree30Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree30Norm x).property (boundaryFullPowerDegree30Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree30Norm,boundaryFullPowerDegree30Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))=(boundaryFullPowerDegree30Block38Norm x).val+(boundaryFullPowerDegree30Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block38Norm x).property (boundaryFullPowerDegree30Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block38Norm,boundaryFullPowerDegree30Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))))=(boundaryFullPowerDegree30Block36Norm x).val+(boundaryFullPowerDegree30Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block36Norm x).property (boundaryFullPowerDegree30Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block36Norm,boundaryFullPowerDegree30Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x)))))))))+(((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x)))))))))+(((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))))))=(boundaryFullPowerDegree30Block31Norm x).val+(boundaryFullPowerDegree30Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block31Norm x).property (boundaryFullPowerDegree30Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block31Norm,boundaryFullPowerDegree30Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree30Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x)))))))))+(((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x)))))))))))+(((((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x)))))))))+(((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x)))))))))+(((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x)))))))))))+(((((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x)))))))))+(((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x))))))))))))=(boundaryFullPowerDegree30Block21Norm x).val+(boundaryFullPowerDegree30Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree30Block21Norm x).property (boundaryFullPowerDegree30Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block21Norm,boundaryFullPowerDegree30Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree30Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 30 x=c} := by

  have he0 : boundaryFullPowerRow77 30 x=((((((((((boundaryRePowerRow77_0 30 x)+(boundaryRePowerRow77_1 30 x)))+(((boundaryRePowerRow77_2 30 x)+(((boundaryRePowerRow77_3 30 x)+(boundaryRePowerRow77_4 30 x)))))))+(((((boundaryRePowerRow77_5 30 x)+(((boundaryRePowerRow77_6 30 x)+(boundaryRePowerRow77_7 30 x)))))+(((boundaryRePowerRow77_8 30 x)+(((boundaryRePowerRow77_9 30 x)+(boundaryRePowerRow77_10 30 x)))))))))+(((((((boundaryRePowerRow77_11 30 x)+(((boundaryRePowerRow77_12 30 x)+(boundaryRePowerRow77_13 30 x)))))+(((boundaryRePowerRow77_14 30 x)+(((boundaryRePowerRow77_15 30 x)+(boundaryRePowerRow77_16 30 x)))))))+(((((boundaryRePowerRow77_17 30 x)+(((boundaryRePowerRow77_18 30 x)+(boundaryRePowerRow77_19 30 x)))))+(((boundaryRePowerRow77_20 30 x)+(((boundaryRePowerRow77_21 30 x)+(boundaryRePowerRow77_22 30 x)))))))))))+(((((((((boundaryImPowerRow77_0 30 x)+(boundaryImPowerRow77_1 30 x)))+(((boundaryImPowerRow77_2 30 x)+(((boundaryImPowerRow77_3 30 x)+(boundaryImPowerRow77_4 30 x)))))))+(((((boundaryImPowerRow77_5 30 x)+(((boundaryImPowerRow77_6 30 x)+(boundaryImPowerRow77_7 30 x)))))+(((boundaryImPowerRow77_8 30 x)+(((boundaryImPowerRow77_9 30 x)+(boundaryImPowerRow77_10 30 x)))))))))+(((((((boundaryImPowerRow77_11 30 x)+(((boundaryImPowerRow77_12 30 x)+(boundaryImPowerRow77_13 30 x)))))+(((boundaryImPowerRow77_14 30 x)+(((boundaryImPowerRow77_15 30 x)+(boundaryImPowerRow77_16 30 x)))))))+(((((boundaryImPowerRow77_17 30 x)+(((boundaryImPowerRow77_18 30 x)+(boundaryImPowerRow77_19 30 x)))))+(((boundaryImPowerRow77_20 30 x)+(((boundaryImPowerRow77_21 30 x)+(boundaryLowPowerRow77 30 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree30Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree30Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
