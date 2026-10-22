import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree37Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree37Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x))=c} := by

  have he : ((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x))=(boundaryRePowerRow77_0Degree37Norm x).val+(boundaryRePowerRow77_1Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree37Norm x).property (boundaryRePowerRow77_1Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree37Norm,boundaryRePowerRow77_1Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x))=c} := by

  have he : ((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x))=(boundaryRePowerRow77_3Degree37Norm x).val+(boundaryRePowerRow77_4Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree37Norm x).property (boundaryRePowerRow77_4Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree37Norm,boundaryRePowerRow77_4Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x))))=(boundaryRePowerRow77_2Degree37Norm x).val+(boundaryFullPowerDegree37Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree37Norm x).property (boundaryFullPowerDegree37Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree37Norm,boundaryFullPowerDegree37Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x))))))=(boundaryFullPowerDegree37Block0Norm x).val+(boundaryFullPowerDegree37Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block0Norm x).property (boundaryFullPowerDegree37Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block0Norm,boundaryFullPowerDegree37Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x))=c} := by

  have he : ((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x))=(boundaryRePowerRow77_6Degree37Norm x).val+(boundaryRePowerRow77_7Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree37Norm x).property (boundaryRePowerRow77_7Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree37Norm,boundaryRePowerRow77_7Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x))))=(boundaryRePowerRow77_5Degree37Norm x).val+(boundaryFullPowerDegree37Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree37Norm x).property (boundaryFullPowerDegree37Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree37Norm,boundaryFullPowerDegree37Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))=c} := by

  have he : ((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))=(boundaryRePowerRow77_9Degree37Norm x).val+(boundaryRePowerRow77_10Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree37Norm x).property (boundaryRePowerRow77_10Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree37Norm,boundaryRePowerRow77_10Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))))=(boundaryRePowerRow77_8Degree37Norm x).val+(boundaryFullPowerDegree37Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree37Norm x).property (boundaryFullPowerDegree37Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree37Norm,boundaryFullPowerDegree37Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))))))=(boundaryFullPowerDegree37Block5Norm x).val+(boundaryFullPowerDegree37Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block5Norm x).property (boundaryFullPowerDegree37Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block5Norm,boundaryFullPowerDegree37Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x))))))))=(boundaryFullPowerDegree37Block3Norm x).val+(boundaryFullPowerDegree37Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block3Norm x).property (boundaryFullPowerDegree37Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block3Norm,boundaryFullPowerDegree37Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x))=c} := by

  have he : ((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x))=(boundaryRePowerRow77_12Degree37Norm x).val+(boundaryRePowerRow77_13Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree37Norm x).property (boundaryRePowerRow77_13Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree37Norm,boundaryRePowerRow77_13Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x))))=(boundaryRePowerRow77_11Degree37Norm x).val+(boundaryFullPowerDegree37Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree37Norm x).property (boundaryFullPowerDegree37Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree37Norm,boundaryFullPowerDegree37Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x))=c} := by

  have he : ((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x))=(boundaryRePowerRow77_15Degree37Norm x).val+(boundaryRePowerRow77_16Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree37Norm x).property (boundaryRePowerRow77_16Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree37Norm,boundaryRePowerRow77_16Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x))))=(boundaryRePowerRow77_14Degree37Norm x).val+(boundaryFullPowerDegree37Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree37Norm x).property (boundaryFullPowerDegree37Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree37Norm,boundaryFullPowerDegree37Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x))))))=(boundaryFullPowerDegree37Block11Norm x).val+(boundaryFullPowerDegree37Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block11Norm x).property (boundaryFullPowerDegree37Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block11Norm,boundaryFullPowerDegree37Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x))=c} := by

  have he : ((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x))=(boundaryRePowerRow77_18Degree37Norm x).val+(boundaryRePowerRow77_19Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree37Norm x).property (boundaryRePowerRow77_19Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree37Norm,boundaryRePowerRow77_19Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x))))=(boundaryRePowerRow77_17Degree37Norm x).val+(boundaryFullPowerDegree37Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree37Norm x).property (boundaryFullPowerDegree37Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree37Norm,boundaryFullPowerDegree37Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))=c} := by

  have he : ((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))=(boundaryRePowerRow77_21Degree37Norm x).val+(boundaryRePowerRow77_22Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree37Norm x).property (boundaryRePowerRow77_22Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree37Norm,boundaryRePowerRow77_22Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))=(boundaryRePowerRow77_20Degree37Norm x).val+(boundaryFullPowerDegree37Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree37Norm x).property (boundaryFullPowerDegree37Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree37Norm,boundaryFullPowerDegree37Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))))=(boundaryFullPowerDegree37Block16Norm x).val+(boundaryFullPowerDegree37Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block16Norm x).property (boundaryFullPowerDegree37Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block16Norm,boundaryFullPowerDegree37Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))))))=(boundaryFullPowerDegree37Block14Norm x).val+(boundaryFullPowerDegree37Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block14Norm x).property (boundaryFullPowerDegree37Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block14Norm,boundaryFullPowerDegree37Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x)))))))))+(((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x)))))))))+(((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x))))))))))=(boundaryFullPowerDegree37Block9Norm x).val+(boundaryFullPowerDegree37Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block9Norm x).property (boundaryFullPowerDegree37Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block9Norm,boundaryFullPowerDegree37Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x))=c} := by

  have he : ((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x))=(boundaryImPowerRow77_0Degree37Norm x).val+(boundaryImPowerRow77_1Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree37Norm x).property (boundaryImPowerRow77_1Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree37Norm,boundaryImPowerRow77_1Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x))=c} := by

  have he : ((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x))=(boundaryImPowerRow77_3Degree37Norm x).val+(boundaryImPowerRow77_4Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree37Norm x).property (boundaryImPowerRow77_4Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree37Norm,boundaryImPowerRow77_4Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x))))=(boundaryImPowerRow77_2Degree37Norm x).val+(boundaryFullPowerDegree37Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree37Norm x).property (boundaryFullPowerDegree37Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree37Norm,boundaryFullPowerDegree37Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x))))))=(boundaryFullPowerDegree37Block22Norm x).val+(boundaryFullPowerDegree37Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block22Norm x).property (boundaryFullPowerDegree37Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block22Norm,boundaryFullPowerDegree37Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x))=c} := by

  have he : ((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x))=(boundaryImPowerRow77_6Degree37Norm x).val+(boundaryImPowerRow77_7Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree37Norm x).property (boundaryImPowerRow77_7Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree37Norm,boundaryImPowerRow77_7Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x))))=(boundaryImPowerRow77_5Degree37Norm x).val+(boundaryFullPowerDegree37Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree37Norm x).property (boundaryFullPowerDegree37Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree37Norm,boundaryFullPowerDegree37Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))=c} := by

  have he : ((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))=(boundaryImPowerRow77_9Degree37Norm x).val+(boundaryImPowerRow77_10Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree37Norm x).property (boundaryImPowerRow77_10Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree37Norm,boundaryImPowerRow77_10Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))))=(boundaryImPowerRow77_8Degree37Norm x).val+(boundaryFullPowerDegree37Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree37Norm x).property (boundaryFullPowerDegree37Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree37Norm,boundaryFullPowerDegree37Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))))))=(boundaryFullPowerDegree37Block27Norm x).val+(boundaryFullPowerDegree37Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block27Norm x).property (boundaryFullPowerDegree37Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block27Norm,boundaryFullPowerDegree37Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x))))))))=(boundaryFullPowerDegree37Block25Norm x).val+(boundaryFullPowerDegree37Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block25Norm x).property (boundaryFullPowerDegree37Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block25Norm,boundaryFullPowerDegree37Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x))=c} := by

  have he : ((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x))=(boundaryImPowerRow77_12Degree37Norm x).val+(boundaryImPowerRow77_13Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree37Norm x).property (boundaryImPowerRow77_13Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree37Norm,boundaryImPowerRow77_13Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x))))=(boundaryImPowerRow77_11Degree37Norm x).val+(boundaryFullPowerDegree37Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree37Norm x).property (boundaryFullPowerDegree37Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree37Norm,boundaryFullPowerDegree37Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x))=c} := by

  have he : ((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x))=(boundaryImPowerRow77_15Degree37Norm x).val+(boundaryImPowerRow77_16Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree37Norm x).property (boundaryImPowerRow77_16Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree37Norm,boundaryImPowerRow77_16Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x))))=(boundaryImPowerRow77_14Degree37Norm x).val+(boundaryFullPowerDegree37Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree37Norm x).property (boundaryFullPowerDegree37Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree37Norm,boundaryFullPowerDegree37Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x))))))=(boundaryFullPowerDegree37Block33Norm x).val+(boundaryFullPowerDegree37Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block33Norm x).property (boundaryFullPowerDegree37Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block33Norm,boundaryFullPowerDegree37Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x))=c} := by

  have he : ((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x))=(boundaryImPowerRow77_18Degree37Norm x).val+(boundaryImPowerRow77_19Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree37Norm x).property (boundaryImPowerRow77_19Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree37Norm,boundaryImPowerRow77_19Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x))))=(boundaryImPowerRow77_17Degree37Norm x).val+(boundaryFullPowerDegree37Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree37Norm x).property (boundaryFullPowerDegree37Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree37Norm,boundaryFullPowerDegree37Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))=c} := by

  have he : ((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))=(boundaryImPowerRow77_21Degree37Norm x).val+(boundaryLowPowerRow77Degree37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree37Norm x).property (boundaryLowPowerRow77Degree37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree37Norm,boundaryLowPowerRow77Degree37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))=(boundaryImPowerRow77_20Degree37Norm x).val+(boundaryFullPowerDegree37Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree37Norm x).property (boundaryFullPowerDegree37Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree37Norm,boundaryFullPowerDegree37Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))=(boundaryFullPowerDegree37Block38Norm x).val+(boundaryFullPowerDegree37Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block38Norm x).property (boundaryFullPowerDegree37Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block38Norm,boundaryFullPowerDegree37Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))))=(boundaryFullPowerDegree37Block36Norm x).val+(boundaryFullPowerDegree37Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block36Norm x).property (boundaryFullPowerDegree37Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block36Norm,boundaryFullPowerDegree37Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x)))))))))+(((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x)))))))))+(((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))))))=(boundaryFullPowerDegree37Block31Norm x).val+(boundaryFullPowerDegree37Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block31Norm x).property (boundaryFullPowerDegree37Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block31Norm,boundaryFullPowerDegree37Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree37Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x)))))))))+(((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x)))))))))))+(((((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x)))))))))+(((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x)))))))))+(((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x)))))))))))+(((((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x)))))))))+(((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x))))))))))))=(boundaryFullPowerDegree37Block21Norm x).val+(boundaryFullPowerDegree37Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree37Block21Norm x).property (boundaryFullPowerDegree37Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block21Norm,boundaryFullPowerDegree37Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree37Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 37 x=c} := by

  have he0 : boundaryFullPowerRow77 37 x=((((((((((boundaryRePowerRow77_0 37 x)+(boundaryRePowerRow77_1 37 x)))+(((boundaryRePowerRow77_2 37 x)+(((boundaryRePowerRow77_3 37 x)+(boundaryRePowerRow77_4 37 x)))))))+(((((boundaryRePowerRow77_5 37 x)+(((boundaryRePowerRow77_6 37 x)+(boundaryRePowerRow77_7 37 x)))))+(((boundaryRePowerRow77_8 37 x)+(((boundaryRePowerRow77_9 37 x)+(boundaryRePowerRow77_10 37 x)))))))))+(((((((boundaryRePowerRow77_11 37 x)+(((boundaryRePowerRow77_12 37 x)+(boundaryRePowerRow77_13 37 x)))))+(((boundaryRePowerRow77_14 37 x)+(((boundaryRePowerRow77_15 37 x)+(boundaryRePowerRow77_16 37 x)))))))+(((((boundaryRePowerRow77_17 37 x)+(((boundaryRePowerRow77_18 37 x)+(boundaryRePowerRow77_19 37 x)))))+(((boundaryRePowerRow77_20 37 x)+(((boundaryRePowerRow77_21 37 x)+(boundaryRePowerRow77_22 37 x)))))))))))+(((((((((boundaryImPowerRow77_0 37 x)+(boundaryImPowerRow77_1 37 x)))+(((boundaryImPowerRow77_2 37 x)+(((boundaryImPowerRow77_3 37 x)+(boundaryImPowerRow77_4 37 x)))))))+(((((boundaryImPowerRow77_5 37 x)+(((boundaryImPowerRow77_6 37 x)+(boundaryImPowerRow77_7 37 x)))))+(((boundaryImPowerRow77_8 37 x)+(((boundaryImPowerRow77_9 37 x)+(boundaryImPowerRow77_10 37 x)))))))))+(((((((boundaryImPowerRow77_11 37 x)+(((boundaryImPowerRow77_12 37 x)+(boundaryImPowerRow77_13 37 x)))))+(((boundaryImPowerRow77_14 37 x)+(((boundaryImPowerRow77_15 37 x)+(boundaryImPowerRow77_16 37 x)))))))+(((((boundaryImPowerRow77_17 37 x)+(((boundaryImPowerRow77_18 37 x)+(boundaryImPowerRow77_19 37 x)))))+(((boundaryImPowerRow77_20 37 x)+(((boundaryImPowerRow77_21 37 x)+(boundaryLowPowerRow77 37 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree37Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree37Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
