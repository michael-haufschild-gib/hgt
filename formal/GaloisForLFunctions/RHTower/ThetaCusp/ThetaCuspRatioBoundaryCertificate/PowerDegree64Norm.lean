import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree64Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree64Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x))=c} := by

  have he : ((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x))=(boundaryRePowerRow77_0Degree64Norm x).val+(boundaryRePowerRow77_1Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree64Norm x).property (boundaryRePowerRow77_1Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree64Norm,boundaryRePowerRow77_1Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x))=c} := by

  have he : ((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x))=(boundaryRePowerRow77_3Degree64Norm x).val+(boundaryRePowerRow77_4Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree64Norm x).property (boundaryRePowerRow77_4Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree64Norm,boundaryRePowerRow77_4Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x))))=(boundaryRePowerRow77_2Degree64Norm x).val+(boundaryFullPowerDegree64Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree64Norm x).property (boundaryFullPowerDegree64Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree64Norm,boundaryFullPowerDegree64Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x))))))=(boundaryFullPowerDegree64Block0Norm x).val+(boundaryFullPowerDegree64Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block0Norm x).property (boundaryFullPowerDegree64Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block0Norm,boundaryFullPowerDegree64Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x))=c} := by

  have he : ((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x))=(boundaryRePowerRow77_6Degree64Norm x).val+(boundaryRePowerRow77_7Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree64Norm x).property (boundaryRePowerRow77_7Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree64Norm,boundaryRePowerRow77_7Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x))))=(boundaryRePowerRow77_5Degree64Norm x).val+(boundaryFullPowerDegree64Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree64Norm x).property (boundaryFullPowerDegree64Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree64Norm,boundaryFullPowerDegree64Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))=c} := by

  have he : ((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))=(boundaryRePowerRow77_9Degree64Norm x).val+(boundaryRePowerRow77_10Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree64Norm x).property (boundaryRePowerRow77_10Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree64Norm,boundaryRePowerRow77_10Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))))=(boundaryRePowerRow77_8Degree64Norm x).val+(boundaryFullPowerDegree64Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree64Norm x).property (boundaryFullPowerDegree64Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree64Norm,boundaryFullPowerDegree64Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))))))=(boundaryFullPowerDegree64Block5Norm x).val+(boundaryFullPowerDegree64Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block5Norm x).property (boundaryFullPowerDegree64Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block5Norm,boundaryFullPowerDegree64Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x))))))))=(boundaryFullPowerDegree64Block3Norm x).val+(boundaryFullPowerDegree64Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block3Norm x).property (boundaryFullPowerDegree64Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block3Norm,boundaryFullPowerDegree64Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x))=c} := by

  have he : ((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x))=(boundaryRePowerRow77_12Degree64Norm x).val+(boundaryRePowerRow77_13Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree64Norm x).property (boundaryRePowerRow77_13Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree64Norm,boundaryRePowerRow77_13Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x))))=(boundaryRePowerRow77_11Degree64Norm x).val+(boundaryFullPowerDegree64Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree64Norm x).property (boundaryFullPowerDegree64Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree64Norm,boundaryFullPowerDegree64Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x))=c} := by

  have he : ((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x))=(boundaryRePowerRow77_15Degree64Norm x).val+(boundaryRePowerRow77_16Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree64Norm x).property (boundaryRePowerRow77_16Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree64Norm,boundaryRePowerRow77_16Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x))))=(boundaryRePowerRow77_14Degree64Norm x).val+(boundaryFullPowerDegree64Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree64Norm x).property (boundaryFullPowerDegree64Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree64Norm,boundaryFullPowerDegree64Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x))))))=(boundaryFullPowerDegree64Block11Norm x).val+(boundaryFullPowerDegree64Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block11Norm x).property (boundaryFullPowerDegree64Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block11Norm,boundaryFullPowerDegree64Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x))=c} := by

  have he : ((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x))=(boundaryRePowerRow77_18Degree64Norm x).val+(boundaryRePowerRow77_19Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree64Norm x).property (boundaryRePowerRow77_19Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree64Norm,boundaryRePowerRow77_19Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x))))=(boundaryRePowerRow77_17Degree64Norm x).val+(boundaryFullPowerDegree64Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree64Norm x).property (boundaryFullPowerDegree64Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree64Norm,boundaryFullPowerDegree64Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))=c} := by

  have he : ((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))=(boundaryRePowerRow77_21Degree64Norm x).val+(boundaryRePowerRow77_22Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree64Norm x).property (boundaryRePowerRow77_22Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree64Norm,boundaryRePowerRow77_22Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))=(boundaryRePowerRow77_20Degree64Norm x).val+(boundaryFullPowerDegree64Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree64Norm x).property (boundaryFullPowerDegree64Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree64Norm,boundaryFullPowerDegree64Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))))=(boundaryFullPowerDegree64Block16Norm x).val+(boundaryFullPowerDegree64Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block16Norm x).property (boundaryFullPowerDegree64Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block16Norm,boundaryFullPowerDegree64Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))))))=(boundaryFullPowerDegree64Block14Norm x).val+(boundaryFullPowerDegree64Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block14Norm x).property (boundaryFullPowerDegree64Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block14Norm,boundaryFullPowerDegree64Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x)))))))))+(((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x)))))))))+(((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x))))))))))=(boundaryFullPowerDegree64Block9Norm x).val+(boundaryFullPowerDegree64Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block9Norm x).property (boundaryFullPowerDegree64Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block9Norm,boundaryFullPowerDegree64Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x))=c} := by

  have he : ((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x))=(boundaryImPowerRow77_0Degree64Norm x).val+(boundaryImPowerRow77_1Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree64Norm x).property (boundaryImPowerRow77_1Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree64Norm,boundaryImPowerRow77_1Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x))=c} := by

  have he : ((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x))=(boundaryImPowerRow77_3Degree64Norm x).val+(boundaryImPowerRow77_4Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree64Norm x).property (boundaryImPowerRow77_4Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree64Norm,boundaryImPowerRow77_4Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x))))=(boundaryImPowerRow77_2Degree64Norm x).val+(boundaryFullPowerDegree64Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree64Norm x).property (boundaryFullPowerDegree64Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree64Norm,boundaryFullPowerDegree64Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x))))))=(boundaryFullPowerDegree64Block22Norm x).val+(boundaryFullPowerDegree64Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block22Norm x).property (boundaryFullPowerDegree64Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block22Norm,boundaryFullPowerDegree64Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x))=c} := by

  have he : ((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x))=(boundaryImPowerRow77_6Degree64Norm x).val+(boundaryImPowerRow77_7Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree64Norm x).property (boundaryImPowerRow77_7Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree64Norm,boundaryImPowerRow77_7Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x))))=(boundaryImPowerRow77_5Degree64Norm x).val+(boundaryFullPowerDegree64Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree64Norm x).property (boundaryFullPowerDegree64Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree64Norm,boundaryFullPowerDegree64Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))=c} := by

  have he : ((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))=(boundaryImPowerRow77_9Degree64Norm x).val+(boundaryImPowerRow77_10Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree64Norm x).property (boundaryImPowerRow77_10Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree64Norm,boundaryImPowerRow77_10Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))))=(boundaryImPowerRow77_8Degree64Norm x).val+(boundaryFullPowerDegree64Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree64Norm x).property (boundaryFullPowerDegree64Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree64Norm,boundaryFullPowerDegree64Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))))))=(boundaryFullPowerDegree64Block27Norm x).val+(boundaryFullPowerDegree64Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block27Norm x).property (boundaryFullPowerDegree64Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block27Norm,boundaryFullPowerDegree64Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x))))))))=(boundaryFullPowerDegree64Block25Norm x).val+(boundaryFullPowerDegree64Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block25Norm x).property (boundaryFullPowerDegree64Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block25Norm,boundaryFullPowerDegree64Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x))=c} := by

  have he : ((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x))=(boundaryImPowerRow77_12Degree64Norm x).val+(boundaryImPowerRow77_13Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree64Norm x).property (boundaryImPowerRow77_13Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree64Norm,boundaryImPowerRow77_13Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x))))=(boundaryImPowerRow77_11Degree64Norm x).val+(boundaryFullPowerDegree64Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree64Norm x).property (boundaryFullPowerDegree64Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree64Norm,boundaryFullPowerDegree64Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x))=c} := by

  have he : ((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x))=(boundaryImPowerRow77_15Degree64Norm x).val+(boundaryImPowerRow77_16Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree64Norm x).property (boundaryImPowerRow77_16Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree64Norm,boundaryImPowerRow77_16Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x))))=(boundaryImPowerRow77_14Degree64Norm x).val+(boundaryFullPowerDegree64Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree64Norm x).property (boundaryFullPowerDegree64Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree64Norm,boundaryFullPowerDegree64Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x))))))=(boundaryFullPowerDegree64Block33Norm x).val+(boundaryFullPowerDegree64Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block33Norm x).property (boundaryFullPowerDegree64Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block33Norm,boundaryFullPowerDegree64Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x))=c} := by

  have he : ((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x))=(boundaryImPowerRow77_18Degree64Norm x).val+(boundaryImPowerRow77_19Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree64Norm x).property (boundaryImPowerRow77_19Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree64Norm,boundaryImPowerRow77_19Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x))))=(boundaryImPowerRow77_17Degree64Norm x).val+(boundaryFullPowerDegree64Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree64Norm x).property (boundaryFullPowerDegree64Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree64Norm,boundaryFullPowerDegree64Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))=c} := by

  have he : ((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))=(boundaryImPowerRow77_21Degree64Norm x).val+(boundaryLowPowerRow77Degree64Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree64Norm x).property (boundaryLowPowerRow77Degree64Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree64Norm,boundaryLowPowerRow77Degree64Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))=(boundaryImPowerRow77_20Degree64Norm x).val+(boundaryFullPowerDegree64Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree64Norm x).property (boundaryFullPowerDegree64Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree64Norm,boundaryFullPowerDegree64Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))=(boundaryFullPowerDegree64Block38Norm x).val+(boundaryFullPowerDegree64Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block38Norm x).property (boundaryFullPowerDegree64Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block38Norm,boundaryFullPowerDegree64Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))))=(boundaryFullPowerDegree64Block36Norm x).val+(boundaryFullPowerDegree64Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block36Norm x).property (boundaryFullPowerDegree64Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block36Norm,boundaryFullPowerDegree64Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x)))))))))+(((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x)))))))))+(((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))))))=(boundaryFullPowerDegree64Block31Norm x).val+(boundaryFullPowerDegree64Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block31Norm x).property (boundaryFullPowerDegree64Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block31Norm,boundaryFullPowerDegree64Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree64Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x)))))))))+(((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x)))))))))))+(((((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x)))))))))+(((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x)))))))))+(((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x)))))))))))+(((((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x)))))))))+(((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x))))))))))))=(boundaryFullPowerDegree64Block21Norm x).val+(boundaryFullPowerDegree64Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree64Block21Norm x).property (boundaryFullPowerDegree64Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block21Norm,boundaryFullPowerDegree64Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree64Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 64 x=c} := by

  have he0 : boundaryFullPowerRow77 64 x=((((((((((boundaryRePowerRow77_0 64 x)+(boundaryRePowerRow77_1 64 x)))+(((boundaryRePowerRow77_2 64 x)+(((boundaryRePowerRow77_3 64 x)+(boundaryRePowerRow77_4 64 x)))))))+(((((boundaryRePowerRow77_5 64 x)+(((boundaryRePowerRow77_6 64 x)+(boundaryRePowerRow77_7 64 x)))))+(((boundaryRePowerRow77_8 64 x)+(((boundaryRePowerRow77_9 64 x)+(boundaryRePowerRow77_10 64 x)))))))))+(((((((boundaryRePowerRow77_11 64 x)+(((boundaryRePowerRow77_12 64 x)+(boundaryRePowerRow77_13 64 x)))))+(((boundaryRePowerRow77_14 64 x)+(((boundaryRePowerRow77_15 64 x)+(boundaryRePowerRow77_16 64 x)))))))+(((((boundaryRePowerRow77_17 64 x)+(((boundaryRePowerRow77_18 64 x)+(boundaryRePowerRow77_19 64 x)))))+(((boundaryRePowerRow77_20 64 x)+(((boundaryRePowerRow77_21 64 x)+(boundaryRePowerRow77_22 64 x)))))))))))+(((((((((boundaryImPowerRow77_0 64 x)+(boundaryImPowerRow77_1 64 x)))+(((boundaryImPowerRow77_2 64 x)+(((boundaryImPowerRow77_3 64 x)+(boundaryImPowerRow77_4 64 x)))))))+(((((boundaryImPowerRow77_5 64 x)+(((boundaryImPowerRow77_6 64 x)+(boundaryImPowerRow77_7 64 x)))))+(((boundaryImPowerRow77_8 64 x)+(((boundaryImPowerRow77_9 64 x)+(boundaryImPowerRow77_10 64 x)))))))))+(((((((boundaryImPowerRow77_11 64 x)+(((boundaryImPowerRow77_12 64 x)+(boundaryImPowerRow77_13 64 x)))))+(((boundaryImPowerRow77_14 64 x)+(((boundaryImPowerRow77_15 64 x)+(boundaryImPowerRow77_16 64 x)))))))+(((((boundaryImPowerRow77_17 64 x)+(((boundaryImPowerRow77_18 64 x)+(boundaryImPowerRow77_19 64 x)))))+(((boundaryImPowerRow77_20 64 x)+(((boundaryImPowerRow77_21 64 x)+(boundaryLowPowerRow77 64 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree64Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree64Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
