import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree58Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree58Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x))=c} := by

  have he : ((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x))=(boundaryRePowerRow77_0Degree58Norm x).val+(boundaryRePowerRow77_1Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree58Norm x).property (boundaryRePowerRow77_1Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree58Norm,boundaryRePowerRow77_1Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x))=c} := by

  have he : ((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x))=(boundaryRePowerRow77_3Degree58Norm x).val+(boundaryRePowerRow77_4Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree58Norm x).property (boundaryRePowerRow77_4Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree58Norm,boundaryRePowerRow77_4Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x))))=(boundaryRePowerRow77_2Degree58Norm x).val+(boundaryFullPowerDegree58Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree58Norm x).property (boundaryFullPowerDegree58Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree58Norm,boundaryFullPowerDegree58Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x))))))=(boundaryFullPowerDegree58Block0Norm x).val+(boundaryFullPowerDegree58Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block0Norm x).property (boundaryFullPowerDegree58Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block0Norm,boundaryFullPowerDegree58Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x))=c} := by

  have he : ((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x))=(boundaryRePowerRow77_6Degree58Norm x).val+(boundaryRePowerRow77_7Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree58Norm x).property (boundaryRePowerRow77_7Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree58Norm,boundaryRePowerRow77_7Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x))))=(boundaryRePowerRow77_5Degree58Norm x).val+(boundaryFullPowerDegree58Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree58Norm x).property (boundaryFullPowerDegree58Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree58Norm,boundaryFullPowerDegree58Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))=c} := by

  have he : ((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))=(boundaryRePowerRow77_9Degree58Norm x).val+(boundaryRePowerRow77_10Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree58Norm x).property (boundaryRePowerRow77_10Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree58Norm,boundaryRePowerRow77_10Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))))=(boundaryRePowerRow77_8Degree58Norm x).val+(boundaryFullPowerDegree58Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree58Norm x).property (boundaryFullPowerDegree58Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree58Norm,boundaryFullPowerDegree58Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))))))=(boundaryFullPowerDegree58Block5Norm x).val+(boundaryFullPowerDegree58Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block5Norm x).property (boundaryFullPowerDegree58Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block5Norm,boundaryFullPowerDegree58Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x))))))))=(boundaryFullPowerDegree58Block3Norm x).val+(boundaryFullPowerDegree58Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block3Norm x).property (boundaryFullPowerDegree58Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block3Norm,boundaryFullPowerDegree58Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x))=c} := by

  have he : ((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x))=(boundaryRePowerRow77_12Degree58Norm x).val+(boundaryRePowerRow77_13Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree58Norm x).property (boundaryRePowerRow77_13Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree58Norm,boundaryRePowerRow77_13Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x))))=(boundaryRePowerRow77_11Degree58Norm x).val+(boundaryFullPowerDegree58Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree58Norm x).property (boundaryFullPowerDegree58Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree58Norm,boundaryFullPowerDegree58Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x))=c} := by

  have he : ((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x))=(boundaryRePowerRow77_15Degree58Norm x).val+(boundaryRePowerRow77_16Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree58Norm x).property (boundaryRePowerRow77_16Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree58Norm,boundaryRePowerRow77_16Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x))))=(boundaryRePowerRow77_14Degree58Norm x).val+(boundaryFullPowerDegree58Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree58Norm x).property (boundaryFullPowerDegree58Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree58Norm,boundaryFullPowerDegree58Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x))))))=(boundaryFullPowerDegree58Block11Norm x).val+(boundaryFullPowerDegree58Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block11Norm x).property (boundaryFullPowerDegree58Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block11Norm,boundaryFullPowerDegree58Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x))=c} := by

  have he : ((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x))=(boundaryRePowerRow77_18Degree58Norm x).val+(boundaryRePowerRow77_19Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree58Norm x).property (boundaryRePowerRow77_19Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree58Norm,boundaryRePowerRow77_19Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x))))=(boundaryRePowerRow77_17Degree58Norm x).val+(boundaryFullPowerDegree58Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree58Norm x).property (boundaryFullPowerDegree58Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree58Norm,boundaryFullPowerDegree58Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))=c} := by

  have he : ((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))=(boundaryRePowerRow77_21Degree58Norm x).val+(boundaryRePowerRow77_22Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree58Norm x).property (boundaryRePowerRow77_22Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree58Norm,boundaryRePowerRow77_22Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))=(boundaryRePowerRow77_20Degree58Norm x).val+(boundaryFullPowerDegree58Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree58Norm x).property (boundaryFullPowerDegree58Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree58Norm,boundaryFullPowerDegree58Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))))=(boundaryFullPowerDegree58Block16Norm x).val+(boundaryFullPowerDegree58Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block16Norm x).property (boundaryFullPowerDegree58Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block16Norm,boundaryFullPowerDegree58Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))))))=(boundaryFullPowerDegree58Block14Norm x).val+(boundaryFullPowerDegree58Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block14Norm x).property (boundaryFullPowerDegree58Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block14Norm,boundaryFullPowerDegree58Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x)))))))))+(((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x)))))))))+(((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x))))))))))=(boundaryFullPowerDegree58Block9Norm x).val+(boundaryFullPowerDegree58Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block9Norm x).property (boundaryFullPowerDegree58Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block9Norm,boundaryFullPowerDegree58Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x))=c} := by

  have he : ((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x))=(boundaryImPowerRow77_0Degree58Norm x).val+(boundaryImPowerRow77_1Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree58Norm x).property (boundaryImPowerRow77_1Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree58Norm,boundaryImPowerRow77_1Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x))=c} := by

  have he : ((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x))=(boundaryImPowerRow77_3Degree58Norm x).val+(boundaryImPowerRow77_4Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree58Norm x).property (boundaryImPowerRow77_4Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree58Norm,boundaryImPowerRow77_4Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x))))=(boundaryImPowerRow77_2Degree58Norm x).val+(boundaryFullPowerDegree58Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree58Norm x).property (boundaryFullPowerDegree58Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree58Norm,boundaryFullPowerDegree58Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x))))))=(boundaryFullPowerDegree58Block22Norm x).val+(boundaryFullPowerDegree58Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block22Norm x).property (boundaryFullPowerDegree58Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block22Norm,boundaryFullPowerDegree58Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x))=c} := by

  have he : ((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x))=(boundaryImPowerRow77_6Degree58Norm x).val+(boundaryImPowerRow77_7Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree58Norm x).property (boundaryImPowerRow77_7Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree58Norm,boundaryImPowerRow77_7Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x))))=(boundaryImPowerRow77_5Degree58Norm x).val+(boundaryFullPowerDegree58Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree58Norm x).property (boundaryFullPowerDegree58Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree58Norm,boundaryFullPowerDegree58Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))=c} := by

  have he : ((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))=(boundaryImPowerRow77_9Degree58Norm x).val+(boundaryImPowerRow77_10Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree58Norm x).property (boundaryImPowerRow77_10Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree58Norm,boundaryImPowerRow77_10Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))))=(boundaryImPowerRow77_8Degree58Norm x).val+(boundaryFullPowerDegree58Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree58Norm x).property (boundaryFullPowerDegree58Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree58Norm,boundaryFullPowerDegree58Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))))))=(boundaryFullPowerDegree58Block27Norm x).val+(boundaryFullPowerDegree58Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block27Norm x).property (boundaryFullPowerDegree58Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block27Norm,boundaryFullPowerDegree58Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x))))))))=(boundaryFullPowerDegree58Block25Norm x).val+(boundaryFullPowerDegree58Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block25Norm x).property (boundaryFullPowerDegree58Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block25Norm,boundaryFullPowerDegree58Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x))=c} := by

  have he : ((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x))=(boundaryImPowerRow77_12Degree58Norm x).val+(boundaryImPowerRow77_13Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree58Norm x).property (boundaryImPowerRow77_13Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree58Norm,boundaryImPowerRow77_13Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x))))=(boundaryImPowerRow77_11Degree58Norm x).val+(boundaryFullPowerDegree58Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree58Norm x).property (boundaryFullPowerDegree58Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree58Norm,boundaryFullPowerDegree58Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x))=c} := by

  have he : ((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x))=(boundaryImPowerRow77_15Degree58Norm x).val+(boundaryImPowerRow77_16Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree58Norm x).property (boundaryImPowerRow77_16Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree58Norm,boundaryImPowerRow77_16Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x))))=(boundaryImPowerRow77_14Degree58Norm x).val+(boundaryFullPowerDegree58Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree58Norm x).property (boundaryFullPowerDegree58Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree58Norm,boundaryFullPowerDegree58Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x))))))=(boundaryFullPowerDegree58Block33Norm x).val+(boundaryFullPowerDegree58Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block33Norm x).property (boundaryFullPowerDegree58Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block33Norm,boundaryFullPowerDegree58Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x))=c} := by

  have he : ((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x))=(boundaryImPowerRow77_18Degree58Norm x).val+(boundaryImPowerRow77_19Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree58Norm x).property (boundaryImPowerRow77_19Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree58Norm,boundaryImPowerRow77_19Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x))))=(boundaryImPowerRow77_17Degree58Norm x).val+(boundaryFullPowerDegree58Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree58Norm x).property (boundaryFullPowerDegree58Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree58Norm,boundaryFullPowerDegree58Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))=c} := by

  have he : ((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))=(boundaryImPowerRow77_21Degree58Norm x).val+(boundaryLowPowerRow77Degree58Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree58Norm x).property (boundaryLowPowerRow77Degree58Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree58Norm,boundaryLowPowerRow77Degree58Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))=(boundaryImPowerRow77_20Degree58Norm x).val+(boundaryFullPowerDegree58Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree58Norm x).property (boundaryFullPowerDegree58Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree58Norm,boundaryFullPowerDegree58Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))=(boundaryFullPowerDegree58Block38Norm x).val+(boundaryFullPowerDegree58Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block38Norm x).property (boundaryFullPowerDegree58Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block38Norm,boundaryFullPowerDegree58Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))))=(boundaryFullPowerDegree58Block36Norm x).val+(boundaryFullPowerDegree58Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block36Norm x).property (boundaryFullPowerDegree58Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block36Norm,boundaryFullPowerDegree58Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x)))))))))+(((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x)))))))))+(((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))))))=(boundaryFullPowerDegree58Block31Norm x).val+(boundaryFullPowerDegree58Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block31Norm x).property (boundaryFullPowerDegree58Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block31Norm,boundaryFullPowerDegree58Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree58Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x)))))))))+(((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x)))))))))))+(((((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x)))))))))+(((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x)))))))))+(((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x)))))))))))+(((((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x)))))))))+(((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x))))))))))))=(boundaryFullPowerDegree58Block21Norm x).val+(boundaryFullPowerDegree58Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree58Block21Norm x).property (boundaryFullPowerDegree58Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block21Norm,boundaryFullPowerDegree58Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree58Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 58 x=c} := by

  have he0 : boundaryFullPowerRow77 58 x=((((((((((boundaryRePowerRow77_0 58 x)+(boundaryRePowerRow77_1 58 x)))+(((boundaryRePowerRow77_2 58 x)+(((boundaryRePowerRow77_3 58 x)+(boundaryRePowerRow77_4 58 x)))))))+(((((boundaryRePowerRow77_5 58 x)+(((boundaryRePowerRow77_6 58 x)+(boundaryRePowerRow77_7 58 x)))))+(((boundaryRePowerRow77_8 58 x)+(((boundaryRePowerRow77_9 58 x)+(boundaryRePowerRow77_10 58 x)))))))))+(((((((boundaryRePowerRow77_11 58 x)+(((boundaryRePowerRow77_12 58 x)+(boundaryRePowerRow77_13 58 x)))))+(((boundaryRePowerRow77_14 58 x)+(((boundaryRePowerRow77_15 58 x)+(boundaryRePowerRow77_16 58 x)))))))+(((((boundaryRePowerRow77_17 58 x)+(((boundaryRePowerRow77_18 58 x)+(boundaryRePowerRow77_19 58 x)))))+(((boundaryRePowerRow77_20 58 x)+(((boundaryRePowerRow77_21 58 x)+(boundaryRePowerRow77_22 58 x)))))))))))+(((((((((boundaryImPowerRow77_0 58 x)+(boundaryImPowerRow77_1 58 x)))+(((boundaryImPowerRow77_2 58 x)+(((boundaryImPowerRow77_3 58 x)+(boundaryImPowerRow77_4 58 x)))))))+(((((boundaryImPowerRow77_5 58 x)+(((boundaryImPowerRow77_6 58 x)+(boundaryImPowerRow77_7 58 x)))))+(((boundaryImPowerRow77_8 58 x)+(((boundaryImPowerRow77_9 58 x)+(boundaryImPowerRow77_10 58 x)))))))))+(((((((boundaryImPowerRow77_11 58 x)+(((boundaryImPowerRow77_12 58 x)+(boundaryImPowerRow77_13 58 x)))))+(((boundaryImPowerRow77_14 58 x)+(((boundaryImPowerRow77_15 58 x)+(boundaryImPowerRow77_16 58 x)))))))+(((((boundaryImPowerRow77_17 58 x)+(((boundaryImPowerRow77_18 58 x)+(boundaryImPowerRow77_19 58 x)))))+(((boundaryImPowerRow77_20 58 x)+(((boundaryImPowerRow77_21 58 x)+(boundaryLowPowerRow77 58 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree58Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree58Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
