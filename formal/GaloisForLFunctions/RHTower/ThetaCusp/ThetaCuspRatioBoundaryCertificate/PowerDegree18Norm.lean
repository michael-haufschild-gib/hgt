import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree18Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree18Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x))=c} := by

  have he : ((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x))=(boundaryRePowerRow77_0Degree18Norm x).val+(boundaryRePowerRow77_1Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree18Norm x).property (boundaryRePowerRow77_1Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree18Norm,boundaryRePowerRow77_1Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x))=c} := by

  have he : ((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x))=(boundaryRePowerRow77_3Degree18Norm x).val+(boundaryRePowerRow77_4Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree18Norm x).property (boundaryRePowerRow77_4Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree18Norm,boundaryRePowerRow77_4Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x))))=(boundaryRePowerRow77_2Degree18Norm x).val+(boundaryFullPowerDegree18Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree18Norm x).property (boundaryFullPowerDegree18Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree18Norm,boundaryFullPowerDegree18Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x))))))=(boundaryFullPowerDegree18Block0Norm x).val+(boundaryFullPowerDegree18Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block0Norm x).property (boundaryFullPowerDegree18Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block0Norm,boundaryFullPowerDegree18Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x))=c} := by

  have he : ((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x))=(boundaryRePowerRow77_6Degree18Norm x).val+(boundaryRePowerRow77_7Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree18Norm x).property (boundaryRePowerRow77_7Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree18Norm,boundaryRePowerRow77_7Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x))))=(boundaryRePowerRow77_5Degree18Norm x).val+(boundaryFullPowerDegree18Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree18Norm x).property (boundaryFullPowerDegree18Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree18Norm,boundaryFullPowerDegree18Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))=c} := by

  have he : ((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))=(boundaryRePowerRow77_9Degree18Norm x).val+(boundaryRePowerRow77_10Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree18Norm x).property (boundaryRePowerRow77_10Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree18Norm,boundaryRePowerRow77_10Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))))=(boundaryRePowerRow77_8Degree18Norm x).val+(boundaryFullPowerDegree18Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree18Norm x).property (boundaryFullPowerDegree18Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree18Norm,boundaryFullPowerDegree18Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))))))=(boundaryFullPowerDegree18Block5Norm x).val+(boundaryFullPowerDegree18Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block5Norm x).property (boundaryFullPowerDegree18Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block5Norm,boundaryFullPowerDegree18Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x))))))))=(boundaryFullPowerDegree18Block3Norm x).val+(boundaryFullPowerDegree18Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block3Norm x).property (boundaryFullPowerDegree18Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block3Norm,boundaryFullPowerDegree18Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x))=c} := by

  have he : ((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x))=(boundaryRePowerRow77_12Degree18Norm x).val+(boundaryRePowerRow77_13Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree18Norm x).property (boundaryRePowerRow77_13Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree18Norm,boundaryRePowerRow77_13Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x))))=(boundaryRePowerRow77_11Degree18Norm x).val+(boundaryFullPowerDegree18Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree18Norm x).property (boundaryFullPowerDegree18Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree18Norm,boundaryFullPowerDegree18Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x))=c} := by

  have he : ((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x))=(boundaryRePowerRow77_15Degree18Norm x).val+(boundaryRePowerRow77_16Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree18Norm x).property (boundaryRePowerRow77_16Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree18Norm,boundaryRePowerRow77_16Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x))))=(boundaryRePowerRow77_14Degree18Norm x).val+(boundaryFullPowerDegree18Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree18Norm x).property (boundaryFullPowerDegree18Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree18Norm,boundaryFullPowerDegree18Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x))))))=(boundaryFullPowerDegree18Block11Norm x).val+(boundaryFullPowerDegree18Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block11Norm x).property (boundaryFullPowerDegree18Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block11Norm,boundaryFullPowerDegree18Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x))=c} := by

  have he : ((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x))=(boundaryRePowerRow77_18Degree18Norm x).val+(boundaryRePowerRow77_19Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree18Norm x).property (boundaryRePowerRow77_19Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree18Norm,boundaryRePowerRow77_19Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x))))=(boundaryRePowerRow77_17Degree18Norm x).val+(boundaryFullPowerDegree18Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree18Norm x).property (boundaryFullPowerDegree18Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree18Norm,boundaryFullPowerDegree18Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))=c} := by

  have he : ((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))=(boundaryRePowerRow77_21Degree18Norm x).val+(boundaryRePowerRow77_22Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree18Norm x).property (boundaryRePowerRow77_22Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree18Norm,boundaryRePowerRow77_22Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))=(boundaryRePowerRow77_20Degree18Norm x).val+(boundaryFullPowerDegree18Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree18Norm x).property (boundaryFullPowerDegree18Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree18Norm,boundaryFullPowerDegree18Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))))=(boundaryFullPowerDegree18Block16Norm x).val+(boundaryFullPowerDegree18Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block16Norm x).property (boundaryFullPowerDegree18Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block16Norm,boundaryFullPowerDegree18Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))))))=(boundaryFullPowerDegree18Block14Norm x).val+(boundaryFullPowerDegree18Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block14Norm x).property (boundaryFullPowerDegree18Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block14Norm,boundaryFullPowerDegree18Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x)))))))))+(((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x)))))))))+(((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x))))))))))=(boundaryFullPowerDegree18Block9Norm x).val+(boundaryFullPowerDegree18Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block9Norm x).property (boundaryFullPowerDegree18Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block9Norm,boundaryFullPowerDegree18Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x))=c} := by

  have he : ((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x))=(boundaryImPowerRow77_0Degree18Norm x).val+(boundaryImPowerRow77_1Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree18Norm x).property (boundaryImPowerRow77_1Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree18Norm,boundaryImPowerRow77_1Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x))=c} := by

  have he : ((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x))=(boundaryImPowerRow77_3Degree18Norm x).val+(boundaryImPowerRow77_4Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree18Norm x).property (boundaryImPowerRow77_4Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree18Norm,boundaryImPowerRow77_4Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x))))=(boundaryImPowerRow77_2Degree18Norm x).val+(boundaryFullPowerDegree18Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree18Norm x).property (boundaryFullPowerDegree18Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree18Norm,boundaryFullPowerDegree18Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x))))))=(boundaryFullPowerDegree18Block22Norm x).val+(boundaryFullPowerDegree18Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block22Norm x).property (boundaryFullPowerDegree18Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block22Norm,boundaryFullPowerDegree18Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x))=c} := by

  have he : ((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x))=(boundaryImPowerRow77_6Degree18Norm x).val+(boundaryImPowerRow77_7Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree18Norm x).property (boundaryImPowerRow77_7Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree18Norm,boundaryImPowerRow77_7Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x))))=(boundaryImPowerRow77_5Degree18Norm x).val+(boundaryFullPowerDegree18Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree18Norm x).property (boundaryFullPowerDegree18Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree18Norm,boundaryFullPowerDegree18Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))=c} := by

  have he : ((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))=(boundaryImPowerRow77_9Degree18Norm x).val+(boundaryImPowerRow77_10Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree18Norm x).property (boundaryImPowerRow77_10Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree18Norm,boundaryImPowerRow77_10Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))))=(boundaryImPowerRow77_8Degree18Norm x).val+(boundaryFullPowerDegree18Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree18Norm x).property (boundaryFullPowerDegree18Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree18Norm,boundaryFullPowerDegree18Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))))))=(boundaryFullPowerDegree18Block27Norm x).val+(boundaryFullPowerDegree18Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block27Norm x).property (boundaryFullPowerDegree18Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block27Norm,boundaryFullPowerDegree18Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x))))))))=(boundaryFullPowerDegree18Block25Norm x).val+(boundaryFullPowerDegree18Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block25Norm x).property (boundaryFullPowerDegree18Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block25Norm,boundaryFullPowerDegree18Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x))=c} := by

  have he : ((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x))=(boundaryImPowerRow77_12Degree18Norm x).val+(boundaryImPowerRow77_13Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree18Norm x).property (boundaryImPowerRow77_13Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree18Norm,boundaryImPowerRow77_13Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x))))=(boundaryImPowerRow77_11Degree18Norm x).val+(boundaryFullPowerDegree18Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree18Norm x).property (boundaryFullPowerDegree18Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree18Norm,boundaryFullPowerDegree18Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x))=c} := by

  have he : ((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x))=(boundaryImPowerRow77_15Degree18Norm x).val+(boundaryImPowerRow77_16Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree18Norm x).property (boundaryImPowerRow77_16Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree18Norm,boundaryImPowerRow77_16Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x))))=(boundaryImPowerRow77_14Degree18Norm x).val+(boundaryFullPowerDegree18Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree18Norm x).property (boundaryFullPowerDegree18Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree18Norm,boundaryFullPowerDegree18Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x))))))=(boundaryFullPowerDegree18Block33Norm x).val+(boundaryFullPowerDegree18Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block33Norm x).property (boundaryFullPowerDegree18Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block33Norm,boundaryFullPowerDegree18Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x))=c} := by

  have he : ((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x))=(boundaryImPowerRow77_18Degree18Norm x).val+(boundaryImPowerRow77_19Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree18Norm x).property (boundaryImPowerRow77_19Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree18Norm,boundaryImPowerRow77_19Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x))))=(boundaryImPowerRow77_17Degree18Norm x).val+(boundaryFullPowerDegree18Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree18Norm x).property (boundaryFullPowerDegree18Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree18Norm,boundaryFullPowerDegree18Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))=c} := by

  have he : ((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))=(boundaryImPowerRow77_21Degree18Norm x).val+(boundaryLowPowerRow77Degree18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree18Norm x).property (boundaryLowPowerRow77Degree18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree18Norm,boundaryLowPowerRow77Degree18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))=(boundaryImPowerRow77_20Degree18Norm x).val+(boundaryFullPowerDegree18Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree18Norm x).property (boundaryFullPowerDegree18Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree18Norm,boundaryFullPowerDegree18Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))=(boundaryFullPowerDegree18Block38Norm x).val+(boundaryFullPowerDegree18Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block38Norm x).property (boundaryFullPowerDegree18Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block38Norm,boundaryFullPowerDegree18Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))))=(boundaryFullPowerDegree18Block36Norm x).val+(boundaryFullPowerDegree18Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block36Norm x).property (boundaryFullPowerDegree18Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block36Norm,boundaryFullPowerDegree18Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x)))))))))+(((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x)))))))))+(((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))))))=(boundaryFullPowerDegree18Block31Norm x).val+(boundaryFullPowerDegree18Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block31Norm x).property (boundaryFullPowerDegree18Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block31Norm,boundaryFullPowerDegree18Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree18Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x)))))))))+(((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x)))))))))))+(((((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x)))))))))+(((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x)))))))))+(((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x)))))))))))+(((((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x)))))))))+(((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x))))))))))))=(boundaryFullPowerDegree18Block21Norm x).val+(boundaryFullPowerDegree18Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree18Block21Norm x).property (boundaryFullPowerDegree18Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block21Norm,boundaryFullPowerDegree18Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree18Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 18 x=c} := by

  have he0 : boundaryFullPowerRow77 18 x=((((((((((boundaryRePowerRow77_0 18 x)+(boundaryRePowerRow77_1 18 x)))+(((boundaryRePowerRow77_2 18 x)+(((boundaryRePowerRow77_3 18 x)+(boundaryRePowerRow77_4 18 x)))))))+(((((boundaryRePowerRow77_5 18 x)+(((boundaryRePowerRow77_6 18 x)+(boundaryRePowerRow77_7 18 x)))))+(((boundaryRePowerRow77_8 18 x)+(((boundaryRePowerRow77_9 18 x)+(boundaryRePowerRow77_10 18 x)))))))))+(((((((boundaryRePowerRow77_11 18 x)+(((boundaryRePowerRow77_12 18 x)+(boundaryRePowerRow77_13 18 x)))))+(((boundaryRePowerRow77_14 18 x)+(((boundaryRePowerRow77_15 18 x)+(boundaryRePowerRow77_16 18 x)))))))+(((((boundaryRePowerRow77_17 18 x)+(((boundaryRePowerRow77_18 18 x)+(boundaryRePowerRow77_19 18 x)))))+(((boundaryRePowerRow77_20 18 x)+(((boundaryRePowerRow77_21 18 x)+(boundaryRePowerRow77_22 18 x)))))))))))+(((((((((boundaryImPowerRow77_0 18 x)+(boundaryImPowerRow77_1 18 x)))+(((boundaryImPowerRow77_2 18 x)+(((boundaryImPowerRow77_3 18 x)+(boundaryImPowerRow77_4 18 x)))))))+(((((boundaryImPowerRow77_5 18 x)+(((boundaryImPowerRow77_6 18 x)+(boundaryImPowerRow77_7 18 x)))))+(((boundaryImPowerRow77_8 18 x)+(((boundaryImPowerRow77_9 18 x)+(boundaryImPowerRow77_10 18 x)))))))))+(((((((boundaryImPowerRow77_11 18 x)+(((boundaryImPowerRow77_12 18 x)+(boundaryImPowerRow77_13 18 x)))))+(((boundaryImPowerRow77_14 18 x)+(((boundaryImPowerRow77_15 18 x)+(boundaryImPowerRow77_16 18 x)))))))+(((((boundaryImPowerRow77_17 18 x)+(((boundaryImPowerRow77_18 18 x)+(boundaryImPowerRow77_19 18 x)))))+(((boundaryImPowerRow77_20 18 x)+(((boundaryImPowerRow77_21 18 x)+(boundaryLowPowerRow77 18 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree18Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree18Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
