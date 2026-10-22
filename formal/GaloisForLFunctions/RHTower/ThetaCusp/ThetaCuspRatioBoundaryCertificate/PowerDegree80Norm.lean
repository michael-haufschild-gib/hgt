import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.PowerDegree80Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree80Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x))=c} := by

  have he : ((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x))=(boundaryRePowerRow77_0Degree80Norm x).val+(boundaryRePowerRow77_1Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree80Norm x).property (boundaryRePowerRow77_1Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree80Norm,boundaryRePowerRow77_1Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x))=c} := by

  have he : ((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x))=(boundaryRePowerRow77_3Degree80Norm x).val+(boundaryRePowerRow77_4Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree80Norm x).property (boundaryRePowerRow77_4Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree80Norm,boundaryRePowerRow77_4Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x))))=(boundaryRePowerRow77_2Degree80Norm x).val+(boundaryFullPowerDegree80Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree80Norm x).property (boundaryFullPowerDegree80Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree80Norm,boundaryFullPowerDegree80Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x))))))=(boundaryFullPowerDegree80Block0Norm x).val+(boundaryFullPowerDegree80Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block0Norm x).property (boundaryFullPowerDegree80Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block0Norm,boundaryFullPowerDegree80Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x))=c} := by

  have he : ((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x))=(boundaryRePowerRow77_6Degree80Norm x).val+(boundaryRePowerRow77_7Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree80Norm x).property (boundaryRePowerRow77_7Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree80Norm,boundaryRePowerRow77_7Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x))))=(boundaryRePowerRow77_5Degree80Norm x).val+(boundaryFullPowerDegree80Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree80Norm x).property (boundaryFullPowerDegree80Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree80Norm,boundaryFullPowerDegree80Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))=c} := by

  have he : ((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))=(boundaryRePowerRow77_9Degree80Norm x).val+(boundaryRePowerRow77_10Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree80Norm x).property (boundaryRePowerRow77_10Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree80Norm,boundaryRePowerRow77_10Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))))=(boundaryRePowerRow77_8Degree80Norm x).val+(boundaryFullPowerDegree80Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree80Norm x).property (boundaryFullPowerDegree80Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree80Norm,boundaryFullPowerDegree80Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))))))=(boundaryFullPowerDegree80Block5Norm x).val+(boundaryFullPowerDegree80Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block5Norm x).property (boundaryFullPowerDegree80Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block5Norm,boundaryFullPowerDegree80Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x))))))))=(boundaryFullPowerDegree80Block3Norm x).val+(boundaryFullPowerDegree80Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block3Norm x).property (boundaryFullPowerDegree80Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block3Norm,boundaryFullPowerDegree80Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x))=c} := by

  have he : ((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x))=(boundaryRePowerRow77_12Degree80Norm x).val+(boundaryRePowerRow77_13Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree80Norm x).property (boundaryRePowerRow77_13Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree80Norm,boundaryRePowerRow77_13Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x))))=(boundaryRePowerRow77_11Degree80Norm x).val+(boundaryFullPowerDegree80Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree80Norm x).property (boundaryFullPowerDegree80Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree80Norm,boundaryFullPowerDegree80Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x))=c} := by

  have he : ((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x))=(boundaryRePowerRow77_15Degree80Norm x).val+(boundaryRePowerRow77_16Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree80Norm x).property (boundaryRePowerRow77_16Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree80Norm,boundaryRePowerRow77_16Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x))))=(boundaryRePowerRow77_14Degree80Norm x).val+(boundaryFullPowerDegree80Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree80Norm x).property (boundaryFullPowerDegree80Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree80Norm,boundaryFullPowerDegree80Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x))))))=(boundaryFullPowerDegree80Block11Norm x).val+(boundaryFullPowerDegree80Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block11Norm x).property (boundaryFullPowerDegree80Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block11Norm,boundaryFullPowerDegree80Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x))=c} := by

  have he : ((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x))=(boundaryRePowerRow77_18Degree80Norm x).val+(boundaryRePowerRow77_19Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree80Norm x).property (boundaryRePowerRow77_19Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree80Norm,boundaryRePowerRow77_19Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x))))=(boundaryRePowerRow77_17Degree80Norm x).val+(boundaryFullPowerDegree80Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree80Norm x).property (boundaryFullPowerDegree80Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree80Norm,boundaryFullPowerDegree80Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))=c} := by

  have he : ((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))=(boundaryRePowerRow77_21Degree80Norm x).val+(boundaryRePowerRow77_22Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree80Norm x).property (boundaryRePowerRow77_22Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree80Norm,boundaryRePowerRow77_22Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))=(boundaryRePowerRow77_20Degree80Norm x).val+(boundaryFullPowerDegree80Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree80Norm x).property (boundaryFullPowerDegree80Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree80Norm,boundaryFullPowerDegree80Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))))=(boundaryFullPowerDegree80Block16Norm x).val+(boundaryFullPowerDegree80Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block16Norm x).property (boundaryFullPowerDegree80Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block16Norm,boundaryFullPowerDegree80Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))))))=(boundaryFullPowerDegree80Block14Norm x).val+(boundaryFullPowerDegree80Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block14Norm x).property (boundaryFullPowerDegree80Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block14Norm,boundaryFullPowerDegree80Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x)))))))))+(((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x)))))))))+(((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x))))))))))=(boundaryFullPowerDegree80Block9Norm x).val+(boundaryFullPowerDegree80Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block9Norm x).property (boundaryFullPowerDegree80Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block9Norm,boundaryFullPowerDegree80Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x))=c} := by

  have he : ((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x))=(boundaryImPowerRow77_0Degree80Norm x).val+(boundaryImPowerRow77_1Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree80Norm x).property (boundaryImPowerRow77_1Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree80Norm,boundaryImPowerRow77_1Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x))=c} := by

  have he : ((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x))=(boundaryImPowerRow77_3Degree80Norm x).val+(boundaryImPowerRow77_4Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree80Norm x).property (boundaryImPowerRow77_4Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree80Norm,boundaryImPowerRow77_4Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x))))=(boundaryImPowerRow77_2Degree80Norm x).val+(boundaryFullPowerDegree80Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree80Norm x).property (boundaryFullPowerDegree80Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree80Norm,boundaryFullPowerDegree80Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x))))))=(boundaryFullPowerDegree80Block22Norm x).val+(boundaryFullPowerDegree80Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block22Norm x).property (boundaryFullPowerDegree80Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block22Norm,boundaryFullPowerDegree80Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x))=c} := by

  have he : ((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x))=(boundaryImPowerRow77_6Degree80Norm x).val+(boundaryImPowerRow77_7Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree80Norm x).property (boundaryImPowerRow77_7Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree80Norm,boundaryImPowerRow77_7Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x))))=(boundaryImPowerRow77_5Degree80Norm x).val+(boundaryFullPowerDegree80Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree80Norm x).property (boundaryFullPowerDegree80Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree80Norm,boundaryFullPowerDegree80Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))=c} := by

  have he : ((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))=(boundaryImPowerRow77_9Degree80Norm x).val+(boundaryImPowerRow77_10Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree80Norm x).property (boundaryImPowerRow77_10Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree80Norm,boundaryImPowerRow77_10Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))))=(boundaryImPowerRow77_8Degree80Norm x).val+(boundaryFullPowerDegree80Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree80Norm x).property (boundaryFullPowerDegree80Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree80Norm,boundaryFullPowerDegree80Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))))))=(boundaryFullPowerDegree80Block27Norm x).val+(boundaryFullPowerDegree80Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block27Norm x).property (boundaryFullPowerDegree80Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block27Norm,boundaryFullPowerDegree80Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x))))))))=(boundaryFullPowerDegree80Block25Norm x).val+(boundaryFullPowerDegree80Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block25Norm x).property (boundaryFullPowerDegree80Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block25Norm,boundaryFullPowerDegree80Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x))=c} := by

  have he : ((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x))=(boundaryImPowerRow77_12Degree80Norm x).val+(boundaryImPowerRow77_13Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree80Norm x).property (boundaryImPowerRow77_13Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree80Norm,boundaryImPowerRow77_13Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x))))=(boundaryImPowerRow77_11Degree80Norm x).val+(boundaryFullPowerDegree80Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree80Norm x).property (boundaryFullPowerDegree80Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree80Norm,boundaryFullPowerDegree80Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x))=c} := by

  have he : ((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x))=(boundaryImPowerRow77_15Degree80Norm x).val+(boundaryImPowerRow77_16Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree80Norm x).property (boundaryImPowerRow77_16Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree80Norm,boundaryImPowerRow77_16Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x))))=(boundaryImPowerRow77_14Degree80Norm x).val+(boundaryFullPowerDegree80Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree80Norm x).property (boundaryFullPowerDegree80Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree80Norm,boundaryFullPowerDegree80Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x))))))=(boundaryFullPowerDegree80Block33Norm x).val+(boundaryFullPowerDegree80Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block33Norm x).property (boundaryFullPowerDegree80Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block33Norm,boundaryFullPowerDegree80Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x))=c} := by

  have he : ((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x))=(boundaryImPowerRow77_18Degree80Norm x).val+(boundaryImPowerRow77_19Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree80Norm x).property (boundaryImPowerRow77_19Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree80Norm,boundaryImPowerRow77_19Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x))))=(boundaryImPowerRow77_17Degree80Norm x).val+(boundaryFullPowerDegree80Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree80Norm x).property (boundaryFullPowerDegree80Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree80Norm,boundaryFullPowerDegree80Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))=c} := by

  have he : ((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))=(boundaryImPowerRow77_21Degree80Norm x).val+(boundaryLowPowerRow77Degree80Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree80Norm x).property (boundaryLowPowerRow77Degree80Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree80Norm,boundaryLowPowerRow77Degree80Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))=(boundaryImPowerRow77_20Degree80Norm x).val+(boundaryFullPowerDegree80Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree80Norm x).property (boundaryFullPowerDegree80Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree80Norm,boundaryFullPowerDegree80Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))=(boundaryFullPowerDegree80Block38Norm x).val+(boundaryFullPowerDegree80Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block38Norm x).property (boundaryFullPowerDegree80Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block38Norm,boundaryFullPowerDegree80Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))))=(boundaryFullPowerDegree80Block36Norm x).val+(boundaryFullPowerDegree80Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block36Norm x).property (boundaryFullPowerDegree80Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block36Norm,boundaryFullPowerDegree80Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x)))))))))+(((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x)))))))))+(((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))))))=(boundaryFullPowerDegree80Block31Norm x).val+(boundaryFullPowerDegree80Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block31Norm x).property (boundaryFullPowerDegree80Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block31Norm,boundaryFullPowerDegree80Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree80Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x)))))))))+(((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x)))))))))))+(((((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x)))))))))+(((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x)))))))))+(((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x)))))))))))+(((((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x)))))))))+(((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x))))))))))))=(boundaryFullPowerDegree80Block21Norm x).val+(boundaryFullPowerDegree80Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree80Block21Norm x).property (boundaryFullPowerDegree80Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block21Norm,boundaryFullPowerDegree80Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree80Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 80 x=c} := by

  have he0 : boundaryFullPowerRow77 80 x=((((((((((boundaryRePowerRow77_0 80 x)+(boundaryRePowerRow77_1 80 x)))+(((boundaryRePowerRow77_2 80 x)+(((boundaryRePowerRow77_3 80 x)+(boundaryRePowerRow77_4 80 x)))))))+(((((boundaryRePowerRow77_5 80 x)+(((boundaryRePowerRow77_6 80 x)+(boundaryRePowerRow77_7 80 x)))))+(((boundaryRePowerRow77_8 80 x)+(((boundaryRePowerRow77_9 80 x)+(boundaryRePowerRow77_10 80 x)))))))))+(((((((boundaryRePowerRow77_11 80 x)+(((boundaryRePowerRow77_12 80 x)+(boundaryRePowerRow77_13 80 x)))))+(((boundaryRePowerRow77_14 80 x)+(((boundaryRePowerRow77_15 80 x)+(boundaryRePowerRow77_16 80 x)))))))+(((((boundaryRePowerRow77_17 80 x)+(((boundaryRePowerRow77_18 80 x)+(boundaryRePowerRow77_19 80 x)))))+(((boundaryRePowerRow77_20 80 x)+(((boundaryRePowerRow77_21 80 x)+(boundaryRePowerRow77_22 80 x)))))))))))+(((((((((boundaryImPowerRow77_0 80 x)+(boundaryImPowerRow77_1 80 x)))+(((boundaryImPowerRow77_2 80 x)+(((boundaryImPowerRow77_3 80 x)+(boundaryImPowerRow77_4 80 x)))))))+(((((boundaryImPowerRow77_5 80 x)+(((boundaryImPowerRow77_6 80 x)+(boundaryImPowerRow77_7 80 x)))))+(((boundaryImPowerRow77_8 80 x)+(((boundaryImPowerRow77_9 80 x)+(boundaryImPowerRow77_10 80 x)))))))))+(((((((boundaryImPowerRow77_11 80 x)+(((boundaryImPowerRow77_12 80 x)+(boundaryImPowerRow77_13 80 x)))))+(((boundaryImPowerRow77_14 80 x)+(((boundaryImPowerRow77_15 80 x)+(boundaryImPowerRow77_16 80 x)))))))+(((((boundaryImPowerRow77_17 80 x)+(((boundaryImPowerRow77_18 80 x)+(boundaryImPowerRow77_19 80 x)))))+(((boundaryImPowerRow77_20 80 x)+(((boundaryImPowerRow77_21 80 x)+(boundaryLowPowerRow77 80 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree80Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree80Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
