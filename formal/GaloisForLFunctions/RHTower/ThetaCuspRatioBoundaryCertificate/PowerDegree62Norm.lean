import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree62Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree62Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x))=c} := by

  have he : ((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x))=(boundaryRePowerRow77_0Degree62Norm x).val+(boundaryRePowerRow77_1Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree62Norm x).property (boundaryRePowerRow77_1Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree62Norm,boundaryRePowerRow77_1Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x))=c} := by

  have he : ((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x))=(boundaryRePowerRow77_3Degree62Norm x).val+(boundaryRePowerRow77_4Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree62Norm x).property (boundaryRePowerRow77_4Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree62Norm,boundaryRePowerRow77_4Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x))))=(boundaryRePowerRow77_2Degree62Norm x).val+(boundaryFullPowerDegree62Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree62Norm x).property (boundaryFullPowerDegree62Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree62Norm,boundaryFullPowerDegree62Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x))))))=(boundaryFullPowerDegree62Block0Norm x).val+(boundaryFullPowerDegree62Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block0Norm x).property (boundaryFullPowerDegree62Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block0Norm,boundaryFullPowerDegree62Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x))=c} := by

  have he : ((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x))=(boundaryRePowerRow77_6Degree62Norm x).val+(boundaryRePowerRow77_7Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree62Norm x).property (boundaryRePowerRow77_7Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree62Norm,boundaryRePowerRow77_7Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x))))=(boundaryRePowerRow77_5Degree62Norm x).val+(boundaryFullPowerDegree62Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree62Norm x).property (boundaryFullPowerDegree62Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree62Norm,boundaryFullPowerDegree62Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))=c} := by

  have he : ((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))=(boundaryRePowerRow77_9Degree62Norm x).val+(boundaryRePowerRow77_10Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree62Norm x).property (boundaryRePowerRow77_10Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree62Norm,boundaryRePowerRow77_10Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))))=(boundaryRePowerRow77_8Degree62Norm x).val+(boundaryFullPowerDegree62Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree62Norm x).property (boundaryFullPowerDegree62Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree62Norm,boundaryFullPowerDegree62Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))))))=(boundaryFullPowerDegree62Block5Norm x).val+(boundaryFullPowerDegree62Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block5Norm x).property (boundaryFullPowerDegree62Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block5Norm,boundaryFullPowerDegree62Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x))))))))=(boundaryFullPowerDegree62Block3Norm x).val+(boundaryFullPowerDegree62Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block3Norm x).property (boundaryFullPowerDegree62Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block3Norm,boundaryFullPowerDegree62Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x))=c} := by

  have he : ((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x))=(boundaryRePowerRow77_12Degree62Norm x).val+(boundaryRePowerRow77_13Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree62Norm x).property (boundaryRePowerRow77_13Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree62Norm,boundaryRePowerRow77_13Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x))))=(boundaryRePowerRow77_11Degree62Norm x).val+(boundaryFullPowerDegree62Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree62Norm x).property (boundaryFullPowerDegree62Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree62Norm,boundaryFullPowerDegree62Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x))=c} := by

  have he : ((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x))=(boundaryRePowerRow77_15Degree62Norm x).val+(boundaryRePowerRow77_16Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree62Norm x).property (boundaryRePowerRow77_16Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree62Norm,boundaryRePowerRow77_16Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x))))=(boundaryRePowerRow77_14Degree62Norm x).val+(boundaryFullPowerDegree62Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree62Norm x).property (boundaryFullPowerDegree62Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree62Norm,boundaryFullPowerDegree62Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x))))))=(boundaryFullPowerDegree62Block11Norm x).val+(boundaryFullPowerDegree62Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block11Norm x).property (boundaryFullPowerDegree62Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block11Norm,boundaryFullPowerDegree62Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x))=c} := by

  have he : ((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x))=(boundaryRePowerRow77_18Degree62Norm x).val+(boundaryRePowerRow77_19Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree62Norm x).property (boundaryRePowerRow77_19Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree62Norm,boundaryRePowerRow77_19Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x))))=(boundaryRePowerRow77_17Degree62Norm x).val+(boundaryFullPowerDegree62Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree62Norm x).property (boundaryFullPowerDegree62Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree62Norm,boundaryFullPowerDegree62Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))=c} := by

  have he : ((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))=(boundaryRePowerRow77_21Degree62Norm x).val+(boundaryRePowerRow77_22Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree62Norm x).property (boundaryRePowerRow77_22Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree62Norm,boundaryRePowerRow77_22Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))=(boundaryRePowerRow77_20Degree62Norm x).val+(boundaryFullPowerDegree62Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree62Norm x).property (boundaryFullPowerDegree62Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree62Norm,boundaryFullPowerDegree62Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))))=(boundaryFullPowerDegree62Block16Norm x).val+(boundaryFullPowerDegree62Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block16Norm x).property (boundaryFullPowerDegree62Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block16Norm,boundaryFullPowerDegree62Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))))))=(boundaryFullPowerDegree62Block14Norm x).val+(boundaryFullPowerDegree62Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block14Norm x).property (boundaryFullPowerDegree62Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block14Norm,boundaryFullPowerDegree62Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x)))))))))+(((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x)))))))))+(((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x))))))))))=(boundaryFullPowerDegree62Block9Norm x).val+(boundaryFullPowerDegree62Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block9Norm x).property (boundaryFullPowerDegree62Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block9Norm,boundaryFullPowerDegree62Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x))=c} := by

  have he : ((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x))=(boundaryImPowerRow77_0Degree62Norm x).val+(boundaryImPowerRow77_1Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree62Norm x).property (boundaryImPowerRow77_1Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree62Norm,boundaryImPowerRow77_1Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x))=c} := by

  have he : ((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x))=(boundaryImPowerRow77_3Degree62Norm x).val+(boundaryImPowerRow77_4Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree62Norm x).property (boundaryImPowerRow77_4Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree62Norm,boundaryImPowerRow77_4Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x))))=(boundaryImPowerRow77_2Degree62Norm x).val+(boundaryFullPowerDegree62Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree62Norm x).property (boundaryFullPowerDegree62Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree62Norm,boundaryFullPowerDegree62Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x))))))=(boundaryFullPowerDegree62Block22Norm x).val+(boundaryFullPowerDegree62Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block22Norm x).property (boundaryFullPowerDegree62Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block22Norm,boundaryFullPowerDegree62Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x))=c} := by

  have he : ((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x))=(boundaryImPowerRow77_6Degree62Norm x).val+(boundaryImPowerRow77_7Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree62Norm x).property (boundaryImPowerRow77_7Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree62Norm,boundaryImPowerRow77_7Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x))))=(boundaryImPowerRow77_5Degree62Norm x).val+(boundaryFullPowerDegree62Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree62Norm x).property (boundaryFullPowerDegree62Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree62Norm,boundaryFullPowerDegree62Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))=c} := by

  have he : ((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))=(boundaryImPowerRow77_9Degree62Norm x).val+(boundaryImPowerRow77_10Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree62Norm x).property (boundaryImPowerRow77_10Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree62Norm,boundaryImPowerRow77_10Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))))=(boundaryImPowerRow77_8Degree62Norm x).val+(boundaryFullPowerDegree62Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree62Norm x).property (boundaryFullPowerDegree62Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree62Norm,boundaryFullPowerDegree62Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))))))=(boundaryFullPowerDegree62Block27Norm x).val+(boundaryFullPowerDegree62Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block27Norm x).property (boundaryFullPowerDegree62Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block27Norm,boundaryFullPowerDegree62Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x))))))))=(boundaryFullPowerDegree62Block25Norm x).val+(boundaryFullPowerDegree62Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block25Norm x).property (boundaryFullPowerDegree62Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block25Norm,boundaryFullPowerDegree62Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x))=c} := by

  have he : ((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x))=(boundaryImPowerRow77_12Degree62Norm x).val+(boundaryImPowerRow77_13Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree62Norm x).property (boundaryImPowerRow77_13Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree62Norm,boundaryImPowerRow77_13Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x))))=(boundaryImPowerRow77_11Degree62Norm x).val+(boundaryFullPowerDegree62Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree62Norm x).property (boundaryFullPowerDegree62Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree62Norm,boundaryFullPowerDegree62Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x))=c} := by

  have he : ((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x))=(boundaryImPowerRow77_15Degree62Norm x).val+(boundaryImPowerRow77_16Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree62Norm x).property (boundaryImPowerRow77_16Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree62Norm,boundaryImPowerRow77_16Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x))))=(boundaryImPowerRow77_14Degree62Norm x).val+(boundaryFullPowerDegree62Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree62Norm x).property (boundaryFullPowerDegree62Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree62Norm,boundaryFullPowerDegree62Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x))))))=(boundaryFullPowerDegree62Block33Norm x).val+(boundaryFullPowerDegree62Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block33Norm x).property (boundaryFullPowerDegree62Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block33Norm,boundaryFullPowerDegree62Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x))=c} := by

  have he : ((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x))=(boundaryImPowerRow77_18Degree62Norm x).val+(boundaryImPowerRow77_19Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree62Norm x).property (boundaryImPowerRow77_19Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree62Norm,boundaryImPowerRow77_19Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x))))=(boundaryImPowerRow77_17Degree62Norm x).val+(boundaryFullPowerDegree62Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree62Norm x).property (boundaryFullPowerDegree62Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree62Norm,boundaryFullPowerDegree62Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))=c} := by

  have he : ((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))=(boundaryImPowerRow77_21Degree62Norm x).val+(boundaryLowPowerRow77Degree62Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree62Norm x).property (boundaryLowPowerRow77Degree62Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree62Norm,boundaryLowPowerRow77Degree62Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))=(boundaryImPowerRow77_20Degree62Norm x).val+(boundaryFullPowerDegree62Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree62Norm x).property (boundaryFullPowerDegree62Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree62Norm,boundaryFullPowerDegree62Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))=(boundaryFullPowerDegree62Block38Norm x).val+(boundaryFullPowerDegree62Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block38Norm x).property (boundaryFullPowerDegree62Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block38Norm,boundaryFullPowerDegree62Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))))=(boundaryFullPowerDegree62Block36Norm x).val+(boundaryFullPowerDegree62Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block36Norm x).property (boundaryFullPowerDegree62Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block36Norm,boundaryFullPowerDegree62Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x)))))))))+(((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x)))))))))+(((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))))))=(boundaryFullPowerDegree62Block31Norm x).val+(boundaryFullPowerDegree62Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block31Norm x).property (boundaryFullPowerDegree62Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block31Norm,boundaryFullPowerDegree62Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree62Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x)))))))))+(((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x)))))))))))+(((((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x)))))))))+(((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x)))))))))+(((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x)))))))))))+(((((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x)))))))))+(((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x))))))))))))=(boundaryFullPowerDegree62Block21Norm x).val+(boundaryFullPowerDegree62Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree62Block21Norm x).property (boundaryFullPowerDegree62Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block21Norm,boundaryFullPowerDegree62Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree62Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 62 x=c} := by

  have he0 : boundaryFullPowerRow77 62 x=((((((((((boundaryRePowerRow77_0 62 x)+(boundaryRePowerRow77_1 62 x)))+(((boundaryRePowerRow77_2 62 x)+(((boundaryRePowerRow77_3 62 x)+(boundaryRePowerRow77_4 62 x)))))))+(((((boundaryRePowerRow77_5 62 x)+(((boundaryRePowerRow77_6 62 x)+(boundaryRePowerRow77_7 62 x)))))+(((boundaryRePowerRow77_8 62 x)+(((boundaryRePowerRow77_9 62 x)+(boundaryRePowerRow77_10 62 x)))))))))+(((((((boundaryRePowerRow77_11 62 x)+(((boundaryRePowerRow77_12 62 x)+(boundaryRePowerRow77_13 62 x)))))+(((boundaryRePowerRow77_14 62 x)+(((boundaryRePowerRow77_15 62 x)+(boundaryRePowerRow77_16 62 x)))))))+(((((boundaryRePowerRow77_17 62 x)+(((boundaryRePowerRow77_18 62 x)+(boundaryRePowerRow77_19 62 x)))))+(((boundaryRePowerRow77_20 62 x)+(((boundaryRePowerRow77_21 62 x)+(boundaryRePowerRow77_22 62 x)))))))))))+(((((((((boundaryImPowerRow77_0 62 x)+(boundaryImPowerRow77_1 62 x)))+(((boundaryImPowerRow77_2 62 x)+(((boundaryImPowerRow77_3 62 x)+(boundaryImPowerRow77_4 62 x)))))))+(((((boundaryImPowerRow77_5 62 x)+(((boundaryImPowerRow77_6 62 x)+(boundaryImPowerRow77_7 62 x)))))+(((boundaryImPowerRow77_8 62 x)+(((boundaryImPowerRow77_9 62 x)+(boundaryImPowerRow77_10 62 x)))))))))+(((((((boundaryImPowerRow77_11 62 x)+(((boundaryImPowerRow77_12 62 x)+(boundaryImPowerRow77_13 62 x)))))+(((boundaryImPowerRow77_14 62 x)+(((boundaryImPowerRow77_15 62 x)+(boundaryImPowerRow77_16 62 x)))))))+(((((boundaryImPowerRow77_17 62 x)+(((boundaryImPowerRow77_18 62 x)+(boundaryImPowerRow77_19 62 x)))))+(((boundaryImPowerRow77_20 62 x)+(((boundaryImPowerRow77_21 62 x)+(boundaryLowPowerRow77 62 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree62Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree62Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
