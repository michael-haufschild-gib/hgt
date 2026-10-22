import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree84Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree84Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x))=c} := by

  have he : ((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x))=(boundaryRePowerRow77_0Degree84Norm x).val+(boundaryRePowerRow77_1Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree84Norm x).property (boundaryRePowerRow77_1Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree84Norm,boundaryRePowerRow77_1Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x))=c} := by

  have he : ((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x))=(boundaryRePowerRow77_3Degree84Norm x).val+(boundaryRePowerRow77_4Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree84Norm x).property (boundaryRePowerRow77_4Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree84Norm,boundaryRePowerRow77_4Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x))))=(boundaryRePowerRow77_2Degree84Norm x).val+(boundaryFullPowerDegree84Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree84Norm x).property (boundaryFullPowerDegree84Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree84Norm,boundaryFullPowerDegree84Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x))))))=(boundaryFullPowerDegree84Block0Norm x).val+(boundaryFullPowerDegree84Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block0Norm x).property (boundaryFullPowerDegree84Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block0Norm,boundaryFullPowerDegree84Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x))=c} := by

  have he : ((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x))=(boundaryRePowerRow77_6Degree84Norm x).val+(boundaryRePowerRow77_7Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree84Norm x).property (boundaryRePowerRow77_7Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree84Norm,boundaryRePowerRow77_7Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x))))=(boundaryRePowerRow77_5Degree84Norm x).val+(boundaryFullPowerDegree84Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree84Norm x).property (boundaryFullPowerDegree84Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree84Norm,boundaryFullPowerDegree84Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))=c} := by

  have he : ((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))=(boundaryRePowerRow77_9Degree84Norm x).val+(boundaryRePowerRow77_10Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree84Norm x).property (boundaryRePowerRow77_10Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree84Norm,boundaryRePowerRow77_10Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))))=(boundaryRePowerRow77_8Degree84Norm x).val+(boundaryFullPowerDegree84Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree84Norm x).property (boundaryFullPowerDegree84Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree84Norm,boundaryFullPowerDegree84Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))))))=(boundaryFullPowerDegree84Block5Norm x).val+(boundaryFullPowerDegree84Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block5Norm x).property (boundaryFullPowerDegree84Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block5Norm,boundaryFullPowerDegree84Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x))))))))=(boundaryFullPowerDegree84Block3Norm x).val+(boundaryFullPowerDegree84Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block3Norm x).property (boundaryFullPowerDegree84Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block3Norm,boundaryFullPowerDegree84Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x))=c} := by

  have he : ((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x))=(boundaryRePowerRow77_12Degree84Norm x).val+(boundaryRePowerRow77_13Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree84Norm x).property (boundaryRePowerRow77_13Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree84Norm,boundaryRePowerRow77_13Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x))))=(boundaryRePowerRow77_11Degree84Norm x).val+(boundaryFullPowerDegree84Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree84Norm x).property (boundaryFullPowerDegree84Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree84Norm,boundaryFullPowerDegree84Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x))=c} := by

  have he : ((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x))=(boundaryRePowerRow77_15Degree84Norm x).val+(boundaryRePowerRow77_16Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree84Norm x).property (boundaryRePowerRow77_16Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree84Norm,boundaryRePowerRow77_16Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x))))=(boundaryRePowerRow77_14Degree84Norm x).val+(boundaryFullPowerDegree84Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree84Norm x).property (boundaryFullPowerDegree84Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree84Norm,boundaryFullPowerDegree84Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x))))))=(boundaryFullPowerDegree84Block11Norm x).val+(boundaryFullPowerDegree84Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block11Norm x).property (boundaryFullPowerDegree84Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block11Norm,boundaryFullPowerDegree84Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x))=c} := by

  have he : ((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x))=(boundaryRePowerRow77_18Degree84Norm x).val+(boundaryRePowerRow77_19Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree84Norm x).property (boundaryRePowerRow77_19Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree84Norm,boundaryRePowerRow77_19Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x))))=(boundaryRePowerRow77_17Degree84Norm x).val+(boundaryFullPowerDegree84Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree84Norm x).property (boundaryFullPowerDegree84Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree84Norm,boundaryFullPowerDegree84Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))=c} := by

  have he : ((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))=(boundaryRePowerRow77_21Degree84Norm x).val+(boundaryRePowerRow77_22Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree84Norm x).property (boundaryRePowerRow77_22Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree84Norm,boundaryRePowerRow77_22Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))=(boundaryRePowerRow77_20Degree84Norm x).val+(boundaryFullPowerDegree84Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree84Norm x).property (boundaryFullPowerDegree84Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree84Norm,boundaryFullPowerDegree84Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))))=(boundaryFullPowerDegree84Block16Norm x).val+(boundaryFullPowerDegree84Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block16Norm x).property (boundaryFullPowerDegree84Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block16Norm,boundaryFullPowerDegree84Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))))))=(boundaryFullPowerDegree84Block14Norm x).val+(boundaryFullPowerDegree84Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block14Norm x).property (boundaryFullPowerDegree84Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block14Norm,boundaryFullPowerDegree84Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x)))))))))+(((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x)))))))))+(((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x))))))))))=(boundaryFullPowerDegree84Block9Norm x).val+(boundaryFullPowerDegree84Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block9Norm x).property (boundaryFullPowerDegree84Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block9Norm,boundaryFullPowerDegree84Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x))=c} := by

  have he : ((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x))=(boundaryImPowerRow77_0Degree84Norm x).val+(boundaryImPowerRow77_1Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree84Norm x).property (boundaryImPowerRow77_1Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree84Norm,boundaryImPowerRow77_1Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x))=c} := by

  have he : ((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x))=(boundaryImPowerRow77_3Degree84Norm x).val+(boundaryImPowerRow77_4Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree84Norm x).property (boundaryImPowerRow77_4Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree84Norm,boundaryImPowerRow77_4Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x))))=(boundaryImPowerRow77_2Degree84Norm x).val+(boundaryFullPowerDegree84Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree84Norm x).property (boundaryFullPowerDegree84Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree84Norm,boundaryFullPowerDegree84Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x))))))=(boundaryFullPowerDegree84Block22Norm x).val+(boundaryFullPowerDegree84Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block22Norm x).property (boundaryFullPowerDegree84Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block22Norm,boundaryFullPowerDegree84Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x))=c} := by

  have he : ((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x))=(boundaryImPowerRow77_6Degree84Norm x).val+(boundaryImPowerRow77_7Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree84Norm x).property (boundaryImPowerRow77_7Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree84Norm,boundaryImPowerRow77_7Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x))))=(boundaryImPowerRow77_5Degree84Norm x).val+(boundaryFullPowerDegree84Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree84Norm x).property (boundaryFullPowerDegree84Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree84Norm,boundaryFullPowerDegree84Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))=c} := by

  have he : ((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))=(boundaryImPowerRow77_9Degree84Norm x).val+(boundaryImPowerRow77_10Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree84Norm x).property (boundaryImPowerRow77_10Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree84Norm,boundaryImPowerRow77_10Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))))=(boundaryImPowerRow77_8Degree84Norm x).val+(boundaryFullPowerDegree84Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree84Norm x).property (boundaryFullPowerDegree84Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree84Norm,boundaryFullPowerDegree84Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))))))=(boundaryFullPowerDegree84Block27Norm x).val+(boundaryFullPowerDegree84Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block27Norm x).property (boundaryFullPowerDegree84Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block27Norm,boundaryFullPowerDegree84Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x))))))))=(boundaryFullPowerDegree84Block25Norm x).val+(boundaryFullPowerDegree84Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block25Norm x).property (boundaryFullPowerDegree84Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block25Norm,boundaryFullPowerDegree84Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x))=c} := by

  have he : ((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x))=(boundaryImPowerRow77_12Degree84Norm x).val+(boundaryImPowerRow77_13Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree84Norm x).property (boundaryImPowerRow77_13Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree84Norm,boundaryImPowerRow77_13Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x))))=(boundaryImPowerRow77_11Degree84Norm x).val+(boundaryFullPowerDegree84Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree84Norm x).property (boundaryFullPowerDegree84Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree84Norm,boundaryFullPowerDegree84Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x))=c} := by

  have he : ((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x))=(boundaryImPowerRow77_15Degree84Norm x).val+(boundaryImPowerRow77_16Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree84Norm x).property (boundaryImPowerRow77_16Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree84Norm,boundaryImPowerRow77_16Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x))))=(boundaryImPowerRow77_14Degree84Norm x).val+(boundaryFullPowerDegree84Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree84Norm x).property (boundaryFullPowerDegree84Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree84Norm,boundaryFullPowerDegree84Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x))))))=(boundaryFullPowerDegree84Block33Norm x).val+(boundaryFullPowerDegree84Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block33Norm x).property (boundaryFullPowerDegree84Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block33Norm,boundaryFullPowerDegree84Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x))=c} := by

  have he : ((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x))=(boundaryImPowerRow77_18Degree84Norm x).val+(boundaryImPowerRow77_19Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree84Norm x).property (boundaryImPowerRow77_19Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree84Norm,boundaryImPowerRow77_19Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x))))=(boundaryImPowerRow77_17Degree84Norm x).val+(boundaryFullPowerDegree84Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree84Norm x).property (boundaryFullPowerDegree84Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree84Norm,boundaryFullPowerDegree84Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))=c} := by

  have he : ((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))=(boundaryImPowerRow77_21Degree84Norm x).val+(boundaryLowPowerRow77Degree84Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree84Norm x).property (boundaryLowPowerRow77Degree84Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree84Norm,boundaryLowPowerRow77Degree84Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))=(boundaryImPowerRow77_20Degree84Norm x).val+(boundaryFullPowerDegree84Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree84Norm x).property (boundaryFullPowerDegree84Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree84Norm,boundaryFullPowerDegree84Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))=(boundaryFullPowerDegree84Block38Norm x).val+(boundaryFullPowerDegree84Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block38Norm x).property (boundaryFullPowerDegree84Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block38Norm,boundaryFullPowerDegree84Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))))=(boundaryFullPowerDegree84Block36Norm x).val+(boundaryFullPowerDegree84Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block36Norm x).property (boundaryFullPowerDegree84Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block36Norm,boundaryFullPowerDegree84Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x)))))))))+(((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x)))))))))+(((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))))))=(boundaryFullPowerDegree84Block31Norm x).val+(boundaryFullPowerDegree84Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block31Norm x).property (boundaryFullPowerDegree84Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block31Norm,boundaryFullPowerDegree84Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree84Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x)))))))))+(((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x)))))))))))+(((((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x)))))))))+(((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x)))))))))+(((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x)))))))))))+(((((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x)))))))))+(((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x))))))))))))=(boundaryFullPowerDegree84Block21Norm x).val+(boundaryFullPowerDegree84Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree84Block21Norm x).property (boundaryFullPowerDegree84Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block21Norm,boundaryFullPowerDegree84Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree84Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 84 x=c} := by

  have he0 : boundaryFullPowerRow77 84 x=((((((((((boundaryRePowerRow77_0 84 x)+(boundaryRePowerRow77_1 84 x)))+(((boundaryRePowerRow77_2 84 x)+(((boundaryRePowerRow77_3 84 x)+(boundaryRePowerRow77_4 84 x)))))))+(((((boundaryRePowerRow77_5 84 x)+(((boundaryRePowerRow77_6 84 x)+(boundaryRePowerRow77_7 84 x)))))+(((boundaryRePowerRow77_8 84 x)+(((boundaryRePowerRow77_9 84 x)+(boundaryRePowerRow77_10 84 x)))))))))+(((((((boundaryRePowerRow77_11 84 x)+(((boundaryRePowerRow77_12 84 x)+(boundaryRePowerRow77_13 84 x)))))+(((boundaryRePowerRow77_14 84 x)+(((boundaryRePowerRow77_15 84 x)+(boundaryRePowerRow77_16 84 x)))))))+(((((boundaryRePowerRow77_17 84 x)+(((boundaryRePowerRow77_18 84 x)+(boundaryRePowerRow77_19 84 x)))))+(((boundaryRePowerRow77_20 84 x)+(((boundaryRePowerRow77_21 84 x)+(boundaryRePowerRow77_22 84 x)))))))))))+(((((((((boundaryImPowerRow77_0 84 x)+(boundaryImPowerRow77_1 84 x)))+(((boundaryImPowerRow77_2 84 x)+(((boundaryImPowerRow77_3 84 x)+(boundaryImPowerRow77_4 84 x)))))))+(((((boundaryImPowerRow77_5 84 x)+(((boundaryImPowerRow77_6 84 x)+(boundaryImPowerRow77_7 84 x)))))+(((boundaryImPowerRow77_8 84 x)+(((boundaryImPowerRow77_9 84 x)+(boundaryImPowerRow77_10 84 x)))))))))+(((((((boundaryImPowerRow77_11 84 x)+(((boundaryImPowerRow77_12 84 x)+(boundaryImPowerRow77_13 84 x)))))+(((boundaryImPowerRow77_14 84 x)+(((boundaryImPowerRow77_15 84 x)+(boundaryImPowerRow77_16 84 x)))))))+(((((boundaryImPowerRow77_17 84 x)+(((boundaryImPowerRow77_18 84 x)+(boundaryImPowerRow77_19 84 x)))))+(((boundaryImPowerRow77_20 84 x)+(((boundaryImPowerRow77_21 84 x)+(boundaryLowPowerRow77 84 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree84Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree84Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
