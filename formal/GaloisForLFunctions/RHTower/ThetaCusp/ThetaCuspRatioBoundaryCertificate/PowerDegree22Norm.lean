import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree22Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree22Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x))=c} := by

  have he : ((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x))=(boundaryRePowerRow77_0Degree22Norm x).val+(boundaryRePowerRow77_1Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree22Norm x).property (boundaryRePowerRow77_1Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree22Norm,boundaryRePowerRow77_1Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x))=c} := by

  have he : ((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x))=(boundaryRePowerRow77_3Degree22Norm x).val+(boundaryRePowerRow77_4Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree22Norm x).property (boundaryRePowerRow77_4Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree22Norm,boundaryRePowerRow77_4Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x))))=(boundaryRePowerRow77_2Degree22Norm x).val+(boundaryFullPowerDegree22Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree22Norm x).property (boundaryFullPowerDegree22Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree22Norm,boundaryFullPowerDegree22Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x))))))=(boundaryFullPowerDegree22Block0Norm x).val+(boundaryFullPowerDegree22Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block0Norm x).property (boundaryFullPowerDegree22Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block0Norm,boundaryFullPowerDegree22Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x))=c} := by

  have he : ((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x))=(boundaryRePowerRow77_6Degree22Norm x).val+(boundaryRePowerRow77_7Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree22Norm x).property (boundaryRePowerRow77_7Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree22Norm,boundaryRePowerRow77_7Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x))))=(boundaryRePowerRow77_5Degree22Norm x).val+(boundaryFullPowerDegree22Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree22Norm x).property (boundaryFullPowerDegree22Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree22Norm,boundaryFullPowerDegree22Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))=c} := by

  have he : ((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))=(boundaryRePowerRow77_9Degree22Norm x).val+(boundaryRePowerRow77_10Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree22Norm x).property (boundaryRePowerRow77_10Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree22Norm,boundaryRePowerRow77_10Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))))=(boundaryRePowerRow77_8Degree22Norm x).val+(boundaryFullPowerDegree22Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree22Norm x).property (boundaryFullPowerDegree22Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree22Norm,boundaryFullPowerDegree22Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))))))=(boundaryFullPowerDegree22Block5Norm x).val+(boundaryFullPowerDegree22Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block5Norm x).property (boundaryFullPowerDegree22Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block5Norm,boundaryFullPowerDegree22Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x))))))))=(boundaryFullPowerDegree22Block3Norm x).val+(boundaryFullPowerDegree22Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block3Norm x).property (boundaryFullPowerDegree22Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block3Norm,boundaryFullPowerDegree22Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x))=c} := by

  have he : ((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x))=(boundaryRePowerRow77_12Degree22Norm x).val+(boundaryRePowerRow77_13Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree22Norm x).property (boundaryRePowerRow77_13Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree22Norm,boundaryRePowerRow77_13Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x))))=(boundaryRePowerRow77_11Degree22Norm x).val+(boundaryFullPowerDegree22Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree22Norm x).property (boundaryFullPowerDegree22Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree22Norm,boundaryFullPowerDegree22Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x))=c} := by

  have he : ((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x))=(boundaryRePowerRow77_15Degree22Norm x).val+(boundaryRePowerRow77_16Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree22Norm x).property (boundaryRePowerRow77_16Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree22Norm,boundaryRePowerRow77_16Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x))))=(boundaryRePowerRow77_14Degree22Norm x).val+(boundaryFullPowerDegree22Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree22Norm x).property (boundaryFullPowerDegree22Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree22Norm,boundaryFullPowerDegree22Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x))))))=(boundaryFullPowerDegree22Block11Norm x).val+(boundaryFullPowerDegree22Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block11Norm x).property (boundaryFullPowerDegree22Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block11Norm,boundaryFullPowerDegree22Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x))=c} := by

  have he : ((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x))=(boundaryRePowerRow77_18Degree22Norm x).val+(boundaryRePowerRow77_19Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree22Norm x).property (boundaryRePowerRow77_19Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree22Norm,boundaryRePowerRow77_19Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x))))=(boundaryRePowerRow77_17Degree22Norm x).val+(boundaryFullPowerDegree22Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree22Norm x).property (boundaryFullPowerDegree22Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree22Norm,boundaryFullPowerDegree22Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))=c} := by

  have he : ((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))=(boundaryRePowerRow77_21Degree22Norm x).val+(boundaryRePowerRow77_22Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree22Norm x).property (boundaryRePowerRow77_22Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree22Norm,boundaryRePowerRow77_22Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))=(boundaryRePowerRow77_20Degree22Norm x).val+(boundaryFullPowerDegree22Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree22Norm x).property (boundaryFullPowerDegree22Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree22Norm,boundaryFullPowerDegree22Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))))=(boundaryFullPowerDegree22Block16Norm x).val+(boundaryFullPowerDegree22Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block16Norm x).property (boundaryFullPowerDegree22Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block16Norm,boundaryFullPowerDegree22Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))))))=(boundaryFullPowerDegree22Block14Norm x).val+(boundaryFullPowerDegree22Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block14Norm x).property (boundaryFullPowerDegree22Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block14Norm,boundaryFullPowerDegree22Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x)))))))))+(((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x)))))))))+(((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x))))))))))=(boundaryFullPowerDegree22Block9Norm x).val+(boundaryFullPowerDegree22Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block9Norm x).property (boundaryFullPowerDegree22Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block9Norm,boundaryFullPowerDegree22Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x))=c} := by

  have he : ((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x))=(boundaryImPowerRow77_0Degree22Norm x).val+(boundaryImPowerRow77_1Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree22Norm x).property (boundaryImPowerRow77_1Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree22Norm,boundaryImPowerRow77_1Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x))=c} := by

  have he : ((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x))=(boundaryImPowerRow77_3Degree22Norm x).val+(boundaryImPowerRow77_4Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree22Norm x).property (boundaryImPowerRow77_4Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree22Norm,boundaryImPowerRow77_4Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x))))=(boundaryImPowerRow77_2Degree22Norm x).val+(boundaryFullPowerDegree22Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree22Norm x).property (boundaryFullPowerDegree22Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree22Norm,boundaryFullPowerDegree22Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x))))))=(boundaryFullPowerDegree22Block22Norm x).val+(boundaryFullPowerDegree22Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block22Norm x).property (boundaryFullPowerDegree22Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block22Norm,boundaryFullPowerDegree22Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x))=c} := by

  have he : ((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x))=(boundaryImPowerRow77_6Degree22Norm x).val+(boundaryImPowerRow77_7Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree22Norm x).property (boundaryImPowerRow77_7Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree22Norm,boundaryImPowerRow77_7Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x))))=(boundaryImPowerRow77_5Degree22Norm x).val+(boundaryFullPowerDegree22Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree22Norm x).property (boundaryFullPowerDegree22Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree22Norm,boundaryFullPowerDegree22Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))=c} := by

  have he : ((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))=(boundaryImPowerRow77_9Degree22Norm x).val+(boundaryImPowerRow77_10Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree22Norm x).property (boundaryImPowerRow77_10Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree22Norm,boundaryImPowerRow77_10Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))))=(boundaryImPowerRow77_8Degree22Norm x).val+(boundaryFullPowerDegree22Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree22Norm x).property (boundaryFullPowerDegree22Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree22Norm,boundaryFullPowerDegree22Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))))))=(boundaryFullPowerDegree22Block27Norm x).val+(boundaryFullPowerDegree22Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block27Norm x).property (boundaryFullPowerDegree22Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block27Norm,boundaryFullPowerDegree22Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x))))))))=(boundaryFullPowerDegree22Block25Norm x).val+(boundaryFullPowerDegree22Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block25Norm x).property (boundaryFullPowerDegree22Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block25Norm,boundaryFullPowerDegree22Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x))=c} := by

  have he : ((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x))=(boundaryImPowerRow77_12Degree22Norm x).val+(boundaryImPowerRow77_13Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree22Norm x).property (boundaryImPowerRow77_13Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree22Norm,boundaryImPowerRow77_13Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x))))=(boundaryImPowerRow77_11Degree22Norm x).val+(boundaryFullPowerDegree22Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree22Norm x).property (boundaryFullPowerDegree22Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree22Norm,boundaryFullPowerDegree22Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x))=c} := by

  have he : ((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x))=(boundaryImPowerRow77_15Degree22Norm x).val+(boundaryImPowerRow77_16Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree22Norm x).property (boundaryImPowerRow77_16Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree22Norm,boundaryImPowerRow77_16Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x))))=(boundaryImPowerRow77_14Degree22Norm x).val+(boundaryFullPowerDegree22Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree22Norm x).property (boundaryFullPowerDegree22Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree22Norm,boundaryFullPowerDegree22Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x))))))=(boundaryFullPowerDegree22Block33Norm x).val+(boundaryFullPowerDegree22Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block33Norm x).property (boundaryFullPowerDegree22Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block33Norm,boundaryFullPowerDegree22Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x))=c} := by

  have he : ((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x))=(boundaryImPowerRow77_18Degree22Norm x).val+(boundaryImPowerRow77_19Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree22Norm x).property (boundaryImPowerRow77_19Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree22Norm,boundaryImPowerRow77_19Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x))))=(boundaryImPowerRow77_17Degree22Norm x).val+(boundaryFullPowerDegree22Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree22Norm x).property (boundaryFullPowerDegree22Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree22Norm,boundaryFullPowerDegree22Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))=c} := by

  have he : ((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))=(boundaryImPowerRow77_21Degree22Norm x).val+(boundaryLowPowerRow77Degree22Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree22Norm x).property (boundaryLowPowerRow77Degree22Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree22Norm,boundaryLowPowerRow77Degree22Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))=(boundaryImPowerRow77_20Degree22Norm x).val+(boundaryFullPowerDegree22Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree22Norm x).property (boundaryFullPowerDegree22Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree22Norm,boundaryFullPowerDegree22Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))=(boundaryFullPowerDegree22Block38Norm x).val+(boundaryFullPowerDegree22Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block38Norm x).property (boundaryFullPowerDegree22Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block38Norm,boundaryFullPowerDegree22Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))))=(boundaryFullPowerDegree22Block36Norm x).val+(boundaryFullPowerDegree22Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block36Norm x).property (boundaryFullPowerDegree22Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block36Norm,boundaryFullPowerDegree22Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x)))))))))+(((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x)))))))))+(((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))))))=(boundaryFullPowerDegree22Block31Norm x).val+(boundaryFullPowerDegree22Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block31Norm x).property (boundaryFullPowerDegree22Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block31Norm,boundaryFullPowerDegree22Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree22Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x)))))))))+(((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x)))))))))))+(((((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x)))))))))+(((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x)))))))))+(((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x)))))))))))+(((((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x)))))))))+(((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x))))))))))))=(boundaryFullPowerDegree22Block21Norm x).val+(boundaryFullPowerDegree22Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree22Block21Norm x).property (boundaryFullPowerDegree22Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block21Norm,boundaryFullPowerDegree22Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree22Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 22 x=c} := by

  have he0 : boundaryFullPowerRow77 22 x=((((((((((boundaryRePowerRow77_0 22 x)+(boundaryRePowerRow77_1 22 x)))+(((boundaryRePowerRow77_2 22 x)+(((boundaryRePowerRow77_3 22 x)+(boundaryRePowerRow77_4 22 x)))))))+(((((boundaryRePowerRow77_5 22 x)+(((boundaryRePowerRow77_6 22 x)+(boundaryRePowerRow77_7 22 x)))))+(((boundaryRePowerRow77_8 22 x)+(((boundaryRePowerRow77_9 22 x)+(boundaryRePowerRow77_10 22 x)))))))))+(((((((boundaryRePowerRow77_11 22 x)+(((boundaryRePowerRow77_12 22 x)+(boundaryRePowerRow77_13 22 x)))))+(((boundaryRePowerRow77_14 22 x)+(((boundaryRePowerRow77_15 22 x)+(boundaryRePowerRow77_16 22 x)))))))+(((((boundaryRePowerRow77_17 22 x)+(((boundaryRePowerRow77_18 22 x)+(boundaryRePowerRow77_19 22 x)))))+(((boundaryRePowerRow77_20 22 x)+(((boundaryRePowerRow77_21 22 x)+(boundaryRePowerRow77_22 22 x)))))))))))+(((((((((boundaryImPowerRow77_0 22 x)+(boundaryImPowerRow77_1 22 x)))+(((boundaryImPowerRow77_2 22 x)+(((boundaryImPowerRow77_3 22 x)+(boundaryImPowerRow77_4 22 x)))))))+(((((boundaryImPowerRow77_5 22 x)+(((boundaryImPowerRow77_6 22 x)+(boundaryImPowerRow77_7 22 x)))))+(((boundaryImPowerRow77_8 22 x)+(((boundaryImPowerRow77_9 22 x)+(boundaryImPowerRow77_10 22 x)))))))))+(((((((boundaryImPowerRow77_11 22 x)+(((boundaryImPowerRow77_12 22 x)+(boundaryImPowerRow77_13 22 x)))))+(((boundaryImPowerRow77_14 22 x)+(((boundaryImPowerRow77_15 22 x)+(boundaryImPowerRow77_16 22 x)))))))+(((((boundaryImPowerRow77_17 22 x)+(((boundaryImPowerRow77_18 22 x)+(boundaryImPowerRow77_19 22 x)))))+(((boundaryImPowerRow77_20 22 x)+(((boundaryImPowerRow77_21 22 x)+(boundaryLowPowerRow77 22 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree22Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree22Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
