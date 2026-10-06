import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree6Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree6Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x))=c} := by

  have he : ((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x))=(boundaryRePowerRow77_0Degree6Norm x).val+(boundaryRePowerRow77_1Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree6Norm x).property (boundaryRePowerRow77_1Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree6Norm,boundaryRePowerRow77_1Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x))=c} := by

  have he : ((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x))=(boundaryRePowerRow77_3Degree6Norm x).val+(boundaryRePowerRow77_4Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree6Norm x).property (boundaryRePowerRow77_4Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree6Norm,boundaryRePowerRow77_4Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x))))=(boundaryRePowerRow77_2Degree6Norm x).val+(boundaryFullPowerDegree6Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree6Norm x).property (boundaryFullPowerDegree6Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree6Norm,boundaryFullPowerDegree6Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x))))))=(boundaryFullPowerDegree6Block0Norm x).val+(boundaryFullPowerDegree6Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block0Norm x).property (boundaryFullPowerDegree6Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block0Norm,boundaryFullPowerDegree6Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x))=c} := by

  have he : ((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x))=(boundaryRePowerRow77_6Degree6Norm x).val+(boundaryRePowerRow77_7Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree6Norm x).property (boundaryRePowerRow77_7Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree6Norm,boundaryRePowerRow77_7Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x))))=(boundaryRePowerRow77_5Degree6Norm x).val+(boundaryFullPowerDegree6Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree6Norm x).property (boundaryFullPowerDegree6Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree6Norm,boundaryFullPowerDegree6Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))=c} := by

  have he : ((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))=(boundaryRePowerRow77_9Degree6Norm x).val+(boundaryRePowerRow77_10Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree6Norm x).property (boundaryRePowerRow77_10Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree6Norm,boundaryRePowerRow77_10Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))))=(boundaryRePowerRow77_8Degree6Norm x).val+(boundaryFullPowerDegree6Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree6Norm x).property (boundaryFullPowerDegree6Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree6Norm,boundaryFullPowerDegree6Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))))))=(boundaryFullPowerDegree6Block5Norm x).val+(boundaryFullPowerDegree6Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block5Norm x).property (boundaryFullPowerDegree6Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block5Norm,boundaryFullPowerDegree6Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x))))))))=(boundaryFullPowerDegree6Block3Norm x).val+(boundaryFullPowerDegree6Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block3Norm x).property (boundaryFullPowerDegree6Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block3Norm,boundaryFullPowerDegree6Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x))=c} := by

  have he : ((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x))=(boundaryRePowerRow77_12Degree6Norm x).val+(boundaryRePowerRow77_13Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree6Norm x).property (boundaryRePowerRow77_13Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree6Norm,boundaryRePowerRow77_13Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x))))=(boundaryRePowerRow77_11Degree6Norm x).val+(boundaryFullPowerDegree6Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree6Norm x).property (boundaryFullPowerDegree6Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree6Norm,boundaryFullPowerDegree6Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x))=c} := by

  have he : ((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x))=(boundaryRePowerRow77_15Degree6Norm x).val+(boundaryRePowerRow77_16Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree6Norm x).property (boundaryRePowerRow77_16Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree6Norm,boundaryRePowerRow77_16Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x))))=(boundaryRePowerRow77_14Degree6Norm x).val+(boundaryFullPowerDegree6Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree6Norm x).property (boundaryFullPowerDegree6Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree6Norm,boundaryFullPowerDegree6Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x))))))=(boundaryFullPowerDegree6Block11Norm x).val+(boundaryFullPowerDegree6Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block11Norm x).property (boundaryFullPowerDegree6Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block11Norm,boundaryFullPowerDegree6Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x))=c} := by

  have he : ((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x))=(boundaryRePowerRow77_18Degree6Norm x).val+(boundaryRePowerRow77_19Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree6Norm x).property (boundaryRePowerRow77_19Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree6Norm,boundaryRePowerRow77_19Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x))))=(boundaryRePowerRow77_17Degree6Norm x).val+(boundaryFullPowerDegree6Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree6Norm x).property (boundaryFullPowerDegree6Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree6Norm,boundaryFullPowerDegree6Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))=c} := by

  have he : ((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))=(boundaryRePowerRow77_21Degree6Norm x).val+(boundaryRePowerRow77_22Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree6Norm x).property (boundaryRePowerRow77_22Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree6Norm,boundaryRePowerRow77_22Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))=(boundaryRePowerRow77_20Degree6Norm x).val+(boundaryFullPowerDegree6Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree6Norm x).property (boundaryFullPowerDegree6Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree6Norm,boundaryFullPowerDegree6Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))))=(boundaryFullPowerDegree6Block16Norm x).val+(boundaryFullPowerDegree6Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block16Norm x).property (boundaryFullPowerDegree6Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block16Norm,boundaryFullPowerDegree6Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))))))=(boundaryFullPowerDegree6Block14Norm x).val+(boundaryFullPowerDegree6Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block14Norm x).property (boundaryFullPowerDegree6Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block14Norm,boundaryFullPowerDegree6Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x)))))))))+(((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x)))))))))+(((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x))))))))))=(boundaryFullPowerDegree6Block9Norm x).val+(boundaryFullPowerDegree6Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block9Norm x).property (boundaryFullPowerDegree6Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block9Norm,boundaryFullPowerDegree6Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x))=c} := by

  have he : ((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x))=(boundaryImPowerRow77_0Degree6Norm x).val+(boundaryImPowerRow77_1Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree6Norm x).property (boundaryImPowerRow77_1Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree6Norm,boundaryImPowerRow77_1Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x))=c} := by

  have he : ((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x))=(boundaryImPowerRow77_3Degree6Norm x).val+(boundaryImPowerRow77_4Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree6Norm x).property (boundaryImPowerRow77_4Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree6Norm,boundaryImPowerRow77_4Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x))))=(boundaryImPowerRow77_2Degree6Norm x).val+(boundaryFullPowerDegree6Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree6Norm x).property (boundaryFullPowerDegree6Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree6Norm,boundaryFullPowerDegree6Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x))))))=(boundaryFullPowerDegree6Block22Norm x).val+(boundaryFullPowerDegree6Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block22Norm x).property (boundaryFullPowerDegree6Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block22Norm,boundaryFullPowerDegree6Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x))=c} := by

  have he : ((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x))=(boundaryImPowerRow77_6Degree6Norm x).val+(boundaryImPowerRow77_7Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree6Norm x).property (boundaryImPowerRow77_7Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree6Norm,boundaryImPowerRow77_7Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x))))=(boundaryImPowerRow77_5Degree6Norm x).val+(boundaryFullPowerDegree6Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree6Norm x).property (boundaryFullPowerDegree6Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree6Norm,boundaryFullPowerDegree6Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))=c} := by

  have he : ((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))=(boundaryImPowerRow77_9Degree6Norm x).val+(boundaryImPowerRow77_10Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree6Norm x).property (boundaryImPowerRow77_10Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree6Norm,boundaryImPowerRow77_10Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))))=(boundaryImPowerRow77_8Degree6Norm x).val+(boundaryFullPowerDegree6Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree6Norm x).property (boundaryFullPowerDegree6Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree6Norm,boundaryFullPowerDegree6Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))))))=(boundaryFullPowerDegree6Block27Norm x).val+(boundaryFullPowerDegree6Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block27Norm x).property (boundaryFullPowerDegree6Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block27Norm,boundaryFullPowerDegree6Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x))))))))=(boundaryFullPowerDegree6Block25Norm x).val+(boundaryFullPowerDegree6Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block25Norm x).property (boundaryFullPowerDegree6Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block25Norm,boundaryFullPowerDegree6Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x))=c} := by

  have he : ((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x))=(boundaryImPowerRow77_12Degree6Norm x).val+(boundaryImPowerRow77_13Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree6Norm x).property (boundaryImPowerRow77_13Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree6Norm,boundaryImPowerRow77_13Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x))))=(boundaryImPowerRow77_11Degree6Norm x).val+(boundaryFullPowerDegree6Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree6Norm x).property (boundaryFullPowerDegree6Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree6Norm,boundaryFullPowerDegree6Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x))=c} := by

  have he : ((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x))=(boundaryImPowerRow77_15Degree6Norm x).val+(boundaryImPowerRow77_16Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree6Norm x).property (boundaryImPowerRow77_16Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree6Norm,boundaryImPowerRow77_16Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x))))=(boundaryImPowerRow77_14Degree6Norm x).val+(boundaryFullPowerDegree6Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree6Norm x).property (boundaryFullPowerDegree6Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree6Norm,boundaryFullPowerDegree6Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x))))))=(boundaryFullPowerDegree6Block33Norm x).val+(boundaryFullPowerDegree6Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block33Norm x).property (boundaryFullPowerDegree6Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block33Norm,boundaryFullPowerDegree6Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x))=c} := by

  have he : ((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x))=(boundaryImPowerRow77_18Degree6Norm x).val+(boundaryImPowerRow77_19Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree6Norm x).property (boundaryImPowerRow77_19Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree6Norm,boundaryImPowerRow77_19Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x))))=(boundaryImPowerRow77_17Degree6Norm x).val+(boundaryFullPowerDegree6Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree6Norm x).property (boundaryFullPowerDegree6Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree6Norm,boundaryFullPowerDegree6Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))=c} := by

  have he : ((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))=(boundaryImPowerRow77_21Degree6Norm x).val+(boundaryLowPowerRow77Degree6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree6Norm x).property (boundaryLowPowerRow77Degree6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree6Norm,boundaryLowPowerRow77Degree6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))=(boundaryImPowerRow77_20Degree6Norm x).val+(boundaryFullPowerDegree6Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree6Norm x).property (boundaryFullPowerDegree6Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree6Norm,boundaryFullPowerDegree6Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))=(boundaryFullPowerDegree6Block38Norm x).val+(boundaryFullPowerDegree6Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block38Norm x).property (boundaryFullPowerDegree6Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block38Norm,boundaryFullPowerDegree6Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))))=(boundaryFullPowerDegree6Block36Norm x).val+(boundaryFullPowerDegree6Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block36Norm x).property (boundaryFullPowerDegree6Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block36Norm,boundaryFullPowerDegree6Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x)))))))))+(((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x)))))))))+(((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))))))=(boundaryFullPowerDegree6Block31Norm x).val+(boundaryFullPowerDegree6Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block31Norm x).property (boundaryFullPowerDegree6Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block31Norm,boundaryFullPowerDegree6Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree6Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x)))))))))+(((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x)))))))))))+(((((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x)))))))))+(((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x)))))))))+(((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x)))))))))))+(((((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x)))))))))+(((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x))))))))))))=(boundaryFullPowerDegree6Block21Norm x).val+(boundaryFullPowerDegree6Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree6Block21Norm x).property (boundaryFullPowerDegree6Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block21Norm,boundaryFullPowerDegree6Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree6Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 6 x=c} := by

  have he0 : boundaryFullPowerRow77 6 x=((((((((((boundaryRePowerRow77_0 6 x)+(boundaryRePowerRow77_1 6 x)))+(((boundaryRePowerRow77_2 6 x)+(((boundaryRePowerRow77_3 6 x)+(boundaryRePowerRow77_4 6 x)))))))+(((((boundaryRePowerRow77_5 6 x)+(((boundaryRePowerRow77_6 6 x)+(boundaryRePowerRow77_7 6 x)))))+(((boundaryRePowerRow77_8 6 x)+(((boundaryRePowerRow77_9 6 x)+(boundaryRePowerRow77_10 6 x)))))))))+(((((((boundaryRePowerRow77_11 6 x)+(((boundaryRePowerRow77_12 6 x)+(boundaryRePowerRow77_13 6 x)))))+(((boundaryRePowerRow77_14 6 x)+(((boundaryRePowerRow77_15 6 x)+(boundaryRePowerRow77_16 6 x)))))))+(((((boundaryRePowerRow77_17 6 x)+(((boundaryRePowerRow77_18 6 x)+(boundaryRePowerRow77_19 6 x)))))+(((boundaryRePowerRow77_20 6 x)+(((boundaryRePowerRow77_21 6 x)+(boundaryRePowerRow77_22 6 x)))))))))))+(((((((((boundaryImPowerRow77_0 6 x)+(boundaryImPowerRow77_1 6 x)))+(((boundaryImPowerRow77_2 6 x)+(((boundaryImPowerRow77_3 6 x)+(boundaryImPowerRow77_4 6 x)))))))+(((((boundaryImPowerRow77_5 6 x)+(((boundaryImPowerRow77_6 6 x)+(boundaryImPowerRow77_7 6 x)))))+(((boundaryImPowerRow77_8 6 x)+(((boundaryImPowerRow77_9 6 x)+(boundaryImPowerRow77_10 6 x)))))))))+(((((((boundaryImPowerRow77_11 6 x)+(((boundaryImPowerRow77_12 6 x)+(boundaryImPowerRow77_13 6 x)))))+(((boundaryImPowerRow77_14 6 x)+(((boundaryImPowerRow77_15 6 x)+(boundaryImPowerRow77_16 6 x)))))))+(((((boundaryImPowerRow77_17 6 x)+(((boundaryImPowerRow77_18 6 x)+(boundaryImPowerRow77_19 6 x)))))+(((boundaryImPowerRow77_20 6 x)+(((boundaryImPowerRow77_21 6 x)+(boundaryLowPowerRow77 6 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree6Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree6Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
