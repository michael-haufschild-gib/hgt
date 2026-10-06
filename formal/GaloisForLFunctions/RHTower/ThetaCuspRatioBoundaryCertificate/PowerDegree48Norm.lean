import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree48CleanColumns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree48Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x))=c} := by

  have he : ((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x))=(boundaryRePowerRow77_0Degree48Clean x).val+(boundaryRePowerRow77_1Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree48Clean x).property (boundaryRePowerRow77_1Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree48Clean,boundaryRePowerRow77_1Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x))=c} := by

  have he : ((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x))=(boundaryRePowerRow77_3Degree48Clean x).val+(boundaryRePowerRow77_4Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree48Clean x).property (boundaryRePowerRow77_4Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree48Clean,boundaryRePowerRow77_4Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x))))=(boundaryRePowerRow77_2Degree48Clean x).val+(boundaryFullPowerDegree48Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree48Clean x).property (boundaryFullPowerDegree48Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree48Clean,boundaryFullPowerDegree48Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x))))))=(boundaryFullPowerDegree48Block0Norm x).val+(boundaryFullPowerDegree48Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block0Norm x).property (boundaryFullPowerDegree48Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block0Norm,boundaryFullPowerDegree48Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x))=c} := by

  have he : ((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x))=(boundaryRePowerRow77_6Degree48Clean x).val+(boundaryRePowerRow77_7Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree48Clean x).property (boundaryRePowerRow77_7Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree48Clean,boundaryRePowerRow77_7Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x))))=(boundaryRePowerRow77_5Degree48Clean x).val+(boundaryFullPowerDegree48Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree48Clean x).property (boundaryFullPowerDegree48Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree48Clean,boundaryFullPowerDegree48Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))=c} := by

  have he : ((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))=(boundaryRePowerRow77_9Degree48Clean x).val+(boundaryRePowerRow77_10Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree48Clean x).property (boundaryRePowerRow77_10Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree48Clean,boundaryRePowerRow77_10Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))))=(boundaryRePowerRow77_8Degree48Clean x).val+(boundaryFullPowerDegree48Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree48Clean x).property (boundaryFullPowerDegree48Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree48Clean,boundaryFullPowerDegree48Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))))))=(boundaryFullPowerDegree48Block5Norm x).val+(boundaryFullPowerDegree48Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block5Norm x).property (boundaryFullPowerDegree48Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block5Norm,boundaryFullPowerDegree48Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x))))))))=(boundaryFullPowerDegree48Block3Norm x).val+(boundaryFullPowerDegree48Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block3Norm x).property (boundaryFullPowerDegree48Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block3Norm,boundaryFullPowerDegree48Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x))=c} := by

  have he : ((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x))=(boundaryRePowerRow77_12Degree48Clean x).val+(boundaryRePowerRow77_13Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree48Clean x).property (boundaryRePowerRow77_13Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree48Clean,boundaryRePowerRow77_13Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x))))=(boundaryRePowerRow77_11Degree48Clean x).val+(boundaryFullPowerDegree48Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree48Clean x).property (boundaryFullPowerDegree48Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree48Clean,boundaryFullPowerDegree48Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x))=c} := by

  have he : ((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x))=(boundaryRePowerRow77_15Degree48Clean x).val+(boundaryRePowerRow77_16Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree48Clean x).property (boundaryRePowerRow77_16Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree48Clean,boundaryRePowerRow77_16Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x))))=(boundaryRePowerRow77_14Degree48Clean x).val+(boundaryFullPowerDegree48Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree48Clean x).property (boundaryFullPowerDegree48Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree48Clean,boundaryFullPowerDegree48Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x))))))=(boundaryFullPowerDegree48Block11Norm x).val+(boundaryFullPowerDegree48Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block11Norm x).property (boundaryFullPowerDegree48Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block11Norm,boundaryFullPowerDegree48Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x))=c} := by

  have he : ((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x))=(boundaryRePowerRow77_18Degree48Clean x).val+(boundaryRePowerRow77_19Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree48Clean x).property (boundaryRePowerRow77_19Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree48Clean,boundaryRePowerRow77_19Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x))))=(boundaryRePowerRow77_17Degree48Clean x).val+(boundaryFullPowerDegree48Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree48Clean x).property (boundaryFullPowerDegree48Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree48Clean,boundaryFullPowerDegree48Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))=c} := by

  have he : ((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))=(boundaryRePowerRow77_21Degree48Clean x).val+(boundaryRePowerRow77_22Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree48Clean x).property (boundaryRePowerRow77_22Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree48Clean,boundaryRePowerRow77_22Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))=(boundaryRePowerRow77_20Degree48Clean x).val+(boundaryFullPowerDegree48Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree48Clean x).property (boundaryFullPowerDegree48Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree48Clean,boundaryFullPowerDegree48Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))))=(boundaryFullPowerDegree48Block16Norm x).val+(boundaryFullPowerDegree48Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block16Norm x).property (boundaryFullPowerDegree48Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block16Norm,boundaryFullPowerDegree48Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))))))=(boundaryFullPowerDegree48Block14Norm x).val+(boundaryFullPowerDegree48Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block14Norm x).property (boundaryFullPowerDegree48Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block14Norm,boundaryFullPowerDegree48Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x)))))))))+(((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x)))))))))+(((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x))))))))))=(boundaryFullPowerDegree48Block9Norm x).val+(boundaryFullPowerDegree48Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block9Norm x).property (boundaryFullPowerDegree48Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block9Norm,boundaryFullPowerDegree48Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x))=c} := by

  have he : ((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x))=(boundaryImPowerRow77_0Degree48Clean x).val+(boundaryImPowerRow77_1Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree48Clean x).property (boundaryImPowerRow77_1Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree48Clean,boundaryImPowerRow77_1Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x))=c} := by

  have he : ((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x))=(boundaryImPowerRow77_3Degree48Clean x).val+(boundaryImPowerRow77_4Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree48Clean x).property (boundaryImPowerRow77_4Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree48Clean,boundaryImPowerRow77_4Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x))))=(boundaryImPowerRow77_2Degree48Clean x).val+(boundaryFullPowerDegree48Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree48Clean x).property (boundaryFullPowerDegree48Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree48Clean,boundaryFullPowerDegree48Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x))))))=(boundaryFullPowerDegree48Block22Norm x).val+(boundaryFullPowerDegree48Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block22Norm x).property (boundaryFullPowerDegree48Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block22Norm,boundaryFullPowerDegree48Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x))=c} := by

  have he : ((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x))=(boundaryImPowerRow77_6Degree48Clean x).val+(boundaryImPowerRow77_7Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree48Clean x).property (boundaryImPowerRow77_7Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree48Clean,boundaryImPowerRow77_7Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x))))=(boundaryImPowerRow77_5Degree48Clean x).val+(boundaryFullPowerDegree48Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree48Clean x).property (boundaryFullPowerDegree48Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree48Clean,boundaryFullPowerDegree48Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))=c} := by

  have he : ((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))=(boundaryImPowerRow77_9Degree48Clean x).val+(boundaryImPowerRow77_10Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree48Clean x).property (boundaryImPowerRow77_10Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree48Clean,boundaryImPowerRow77_10Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))))=(boundaryImPowerRow77_8Degree48Clean x).val+(boundaryFullPowerDegree48Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree48Clean x).property (boundaryFullPowerDegree48Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree48Clean,boundaryFullPowerDegree48Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))))))=(boundaryFullPowerDegree48Block27Norm x).val+(boundaryFullPowerDegree48Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block27Norm x).property (boundaryFullPowerDegree48Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block27Norm,boundaryFullPowerDegree48Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x))))))))=(boundaryFullPowerDegree48Block25Norm x).val+(boundaryFullPowerDegree48Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block25Norm x).property (boundaryFullPowerDegree48Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block25Norm,boundaryFullPowerDegree48Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x))=c} := by

  have he : ((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x))=(boundaryImPowerRow77_12Degree48Clean x).val+(boundaryImPowerRow77_13Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree48Clean x).property (boundaryImPowerRow77_13Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree48Clean,boundaryImPowerRow77_13Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x))))=(boundaryImPowerRow77_11Degree48Clean x).val+(boundaryFullPowerDegree48Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree48Clean x).property (boundaryFullPowerDegree48Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree48Clean,boundaryFullPowerDegree48Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x))=c} := by

  have he : ((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x))=(boundaryImPowerRow77_15Degree48Clean x).val+(boundaryImPowerRow77_16Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree48Clean x).property (boundaryImPowerRow77_16Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree48Clean,boundaryImPowerRow77_16Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x))))=(boundaryImPowerRow77_14Degree48Clean x).val+(boundaryFullPowerDegree48Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree48Clean x).property (boundaryFullPowerDegree48Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree48Clean,boundaryFullPowerDegree48Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x))))))=(boundaryFullPowerDegree48Block33Norm x).val+(boundaryFullPowerDegree48Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block33Norm x).property (boundaryFullPowerDegree48Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block33Norm,boundaryFullPowerDegree48Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x))=c} := by

  have he : ((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x))=(boundaryImPowerRow77_18Degree48Clean x).val+(boundaryImPowerRow77_19Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree48Clean x).property (boundaryImPowerRow77_19Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree48Clean,boundaryImPowerRow77_19Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x))))=(boundaryImPowerRow77_17Degree48Clean x).val+(boundaryFullPowerDegree48Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree48Clean x).property (boundaryFullPowerDegree48Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree48Clean,boundaryFullPowerDegree48Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))=c} := by

  have he : ((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))=(boundaryImPowerRow77_21Degree48Clean x).val+(boundaryLowPowerRow77Degree48Clean x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree48Clean x).property (boundaryLowPowerRow77Degree48Clean x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree48Clean,boundaryLowPowerRow77Degree48Clean]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))=(boundaryImPowerRow77_20Degree48Clean x).val+(boundaryFullPowerDegree48Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree48Clean x).property (boundaryFullPowerDegree48Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree48Clean,boundaryFullPowerDegree48Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))=(boundaryFullPowerDegree48Block38Norm x).val+(boundaryFullPowerDegree48Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block38Norm x).property (boundaryFullPowerDegree48Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block38Norm,boundaryFullPowerDegree48Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))))=(boundaryFullPowerDegree48Block36Norm x).val+(boundaryFullPowerDegree48Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block36Norm x).property (boundaryFullPowerDegree48Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block36Norm,boundaryFullPowerDegree48Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x)))))))))+(((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x)))))))))+(((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))))))=(boundaryFullPowerDegree48Block31Norm x).val+(boundaryFullPowerDegree48Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block31Norm x).property (boundaryFullPowerDegree48Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block31Norm,boundaryFullPowerDegree48Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree48Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x)))))))))+(((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x)))))))))))+(((((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x)))))))))+(((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x)))))))))+(((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x)))))))))))+(((((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x)))))))))+(((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x))))))))))))=(boundaryFullPowerDegree48Block21Norm x).val+(boundaryFullPowerDegree48Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree48Block21Norm x).property (boundaryFullPowerDegree48Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block21Norm,boundaryFullPowerDegree48Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree48Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 48 x=c} := by

  have he0 : boundaryFullPowerRow77 48 x=((((((((((boundaryRePowerRow77_0 48 x)+(boundaryRePowerRow77_1 48 x)))+(((boundaryRePowerRow77_2 48 x)+(((boundaryRePowerRow77_3 48 x)+(boundaryRePowerRow77_4 48 x)))))))+(((((boundaryRePowerRow77_5 48 x)+(((boundaryRePowerRow77_6 48 x)+(boundaryRePowerRow77_7 48 x)))))+(((boundaryRePowerRow77_8 48 x)+(((boundaryRePowerRow77_9 48 x)+(boundaryRePowerRow77_10 48 x)))))))))+(((((((boundaryRePowerRow77_11 48 x)+(((boundaryRePowerRow77_12 48 x)+(boundaryRePowerRow77_13 48 x)))))+(((boundaryRePowerRow77_14 48 x)+(((boundaryRePowerRow77_15 48 x)+(boundaryRePowerRow77_16 48 x)))))))+(((((boundaryRePowerRow77_17 48 x)+(((boundaryRePowerRow77_18 48 x)+(boundaryRePowerRow77_19 48 x)))))+(((boundaryRePowerRow77_20 48 x)+(((boundaryRePowerRow77_21 48 x)+(boundaryRePowerRow77_22 48 x)))))))))))+(((((((((boundaryImPowerRow77_0 48 x)+(boundaryImPowerRow77_1 48 x)))+(((boundaryImPowerRow77_2 48 x)+(((boundaryImPowerRow77_3 48 x)+(boundaryImPowerRow77_4 48 x)))))))+(((((boundaryImPowerRow77_5 48 x)+(((boundaryImPowerRow77_6 48 x)+(boundaryImPowerRow77_7 48 x)))))+(((boundaryImPowerRow77_8 48 x)+(((boundaryImPowerRow77_9 48 x)+(boundaryImPowerRow77_10 48 x)))))))))+(((((((boundaryImPowerRow77_11 48 x)+(((boundaryImPowerRow77_12 48 x)+(boundaryImPowerRow77_13 48 x)))))+(((boundaryImPowerRow77_14 48 x)+(((boundaryImPowerRow77_15 48 x)+(boundaryImPowerRow77_16 48 x)))))))+(((((boundaryImPowerRow77_17 48 x)+(((boundaryImPowerRow77_18 48 x)+(boundaryImPowerRow77_19 48 x)))))+(((boundaryImPowerRow77_20 48 x)+(((boundaryImPowerRow77_21 48 x)+(boundaryLowPowerRow77 48 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree48Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree48Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
