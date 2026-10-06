import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree19Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerDegree19Block0Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x))=c} := by

  have he : ((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x))=(boundaryRePowerRow77_0Degree19Norm x).val+(boundaryRePowerRow77_1Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_0Degree19Norm x).property (boundaryRePowerRow77_1Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_0Degree19Norm,boundaryRePowerRow77_1Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block1Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x))=c} := by

  have he : ((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x))=(boundaryRePowerRow77_3Degree19Norm x).val+(boundaryRePowerRow77_4Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_3Degree19Norm x).property (boundaryRePowerRow77_4Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_3Degree19Norm,boundaryRePowerRow77_4Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block2Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x))))=(boundaryRePowerRow77_2Degree19Norm x).val+(boundaryFullPowerDegree19Block1Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_2Degree19Norm x).property (boundaryFullPowerDegree19Block1Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_2Degree19Norm,boundaryFullPowerDegree19Block1Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block3Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x))))))=(boundaryFullPowerDegree19Block0Norm x).val+(boundaryFullPowerDegree19Block2Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block0Norm x).property (boundaryFullPowerDegree19Block2Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block0Norm,boundaryFullPowerDegree19Block2Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block4Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x))=c} := by

  have he : ((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x))=(boundaryRePowerRow77_6Degree19Norm x).val+(boundaryRePowerRow77_7Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_6Degree19Norm x).property (boundaryRePowerRow77_7Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_6Degree19Norm,boundaryRePowerRow77_7Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block5Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x))))=(boundaryRePowerRow77_5Degree19Norm x).val+(boundaryFullPowerDegree19Block4Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_5Degree19Norm x).property (boundaryFullPowerDegree19Block4Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_5Degree19Norm,boundaryFullPowerDegree19Block4Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block6Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))=c} := by

  have he : ((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))=(boundaryRePowerRow77_9Degree19Norm x).val+(boundaryRePowerRow77_10Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_9Degree19Norm x).property (boundaryRePowerRow77_10Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_9Degree19Norm,boundaryRePowerRow77_10Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block7Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))))=(boundaryRePowerRow77_8Degree19Norm x).val+(boundaryFullPowerDegree19Block6Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_8Degree19Norm x).property (boundaryFullPowerDegree19Block6Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_8Degree19Norm,boundaryFullPowerDegree19Block6Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block8Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))))))=(boundaryFullPowerDegree19Block5Norm x).val+(boundaryFullPowerDegree19Block7Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block5Norm x).property (boundaryFullPowerDegree19Block7Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block5Norm,boundaryFullPowerDegree19Block7Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block9Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x))))))))=(boundaryFullPowerDegree19Block3Norm x).val+(boundaryFullPowerDegree19Block8Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block3Norm x).property (boundaryFullPowerDegree19Block8Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block3Norm,boundaryFullPowerDegree19Block8Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block10Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x))=c} := by

  have he : ((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x))=(boundaryRePowerRow77_12Degree19Norm x).val+(boundaryRePowerRow77_13Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_12Degree19Norm x).property (boundaryRePowerRow77_13Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_12Degree19Norm,boundaryRePowerRow77_13Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block11Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x))))=(boundaryRePowerRow77_11Degree19Norm x).val+(boundaryFullPowerDegree19Block10Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_11Degree19Norm x).property (boundaryFullPowerDegree19Block10Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_11Degree19Norm,boundaryFullPowerDegree19Block10Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block12Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x))=c} := by

  have he : ((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x))=(boundaryRePowerRow77_15Degree19Norm x).val+(boundaryRePowerRow77_16Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_15Degree19Norm x).property (boundaryRePowerRow77_16Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_15Degree19Norm,boundaryRePowerRow77_16Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block13Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x))))=(boundaryRePowerRow77_14Degree19Norm x).val+(boundaryFullPowerDegree19Block12Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_14Degree19Norm x).property (boundaryFullPowerDegree19Block12Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_14Degree19Norm,boundaryFullPowerDegree19Block12Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block14Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x))))))=(boundaryFullPowerDegree19Block11Norm x).val+(boundaryFullPowerDegree19Block13Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block11Norm x).property (boundaryFullPowerDegree19Block13Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block11Norm,boundaryFullPowerDegree19Block13Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block15Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x))=c} := by

  have he : ((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x))=(boundaryRePowerRow77_18Degree19Norm x).val+(boundaryRePowerRow77_19Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_18Degree19Norm x).property (boundaryRePowerRow77_19Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_18Degree19Norm,boundaryRePowerRow77_19Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block16Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x))))=(boundaryRePowerRow77_17Degree19Norm x).val+(boundaryFullPowerDegree19Block15Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_17Degree19Norm x).property (boundaryFullPowerDegree19Block15Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_17Degree19Norm,boundaryFullPowerDegree19Block15Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block17Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))=c} := by

  have he : ((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))=(boundaryRePowerRow77_21Degree19Norm x).val+(boundaryRePowerRow77_22Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_21Degree19Norm x).property (boundaryRePowerRow77_22Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_21Degree19Norm,boundaryRePowerRow77_22Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block18Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))=c} := by

  have he : ((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))=(boundaryRePowerRow77_20Degree19Norm x).val+(boundaryFullPowerDegree19Block17Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryRePowerRow77_20Degree19Norm x).property (boundaryFullPowerDegree19Block17Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryRePowerRow77_20Degree19Norm,boundaryFullPowerDegree19Block17Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block19Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))))=c} := by

  have he : ((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))))=(boundaryFullPowerDegree19Block16Norm x).val+(boundaryFullPowerDegree19Block18Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block16Norm x).property (boundaryFullPowerDegree19Block18Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block16Norm,boundaryFullPowerDegree19Block18Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block20Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))))))=c} := by

  have he : ((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))))))=(boundaryFullPowerDegree19Block14Norm x).val+(boundaryFullPowerDegree19Block19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block14Norm x).property (boundaryFullPowerDegree19Block19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block14Norm,boundaryFullPowerDegree19Block19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block21Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x)))))))))+(((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))))))))=c} := by

  have he : ((((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x)))))))))+(((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x))))))))))=(boundaryFullPowerDegree19Block9Norm x).val+(boundaryFullPowerDegree19Block20Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block9Norm x).property (boundaryFullPowerDegree19Block20Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block9Norm,boundaryFullPowerDegree19Block20Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block22Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x))=c} := by

  have he : ((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x))=(boundaryImPowerRow77_0Degree19Norm x).val+(boundaryImPowerRow77_1Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_0Degree19Norm x).property (boundaryImPowerRow77_1Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_0Degree19Norm,boundaryImPowerRow77_1Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block23Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x))=c} := by

  have he : ((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x))=(boundaryImPowerRow77_3Degree19Norm x).val+(boundaryImPowerRow77_4Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_3Degree19Norm x).property (boundaryImPowerRow77_4Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_3Degree19Norm,boundaryImPowerRow77_4Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block24Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x))))=(boundaryImPowerRow77_2Degree19Norm x).val+(boundaryFullPowerDegree19Block23Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_2Degree19Norm x).property (boundaryFullPowerDegree19Block23Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_2Degree19Norm,boundaryFullPowerDegree19Block23Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block25Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x))))))=(boundaryFullPowerDegree19Block22Norm x).val+(boundaryFullPowerDegree19Block24Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block22Norm x).property (boundaryFullPowerDegree19Block24Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block22Norm,boundaryFullPowerDegree19Block24Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block26Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x))=c} := by

  have he : ((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x))=(boundaryImPowerRow77_6Degree19Norm x).val+(boundaryImPowerRow77_7Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_6Degree19Norm x).property (boundaryImPowerRow77_7Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_6Degree19Norm,boundaryImPowerRow77_7Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block27Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x))))=(boundaryImPowerRow77_5Degree19Norm x).val+(boundaryFullPowerDegree19Block26Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_5Degree19Norm x).property (boundaryFullPowerDegree19Block26Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_5Degree19Norm,boundaryFullPowerDegree19Block26Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block28Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))=c} := by

  have he : ((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))=(boundaryImPowerRow77_9Degree19Norm x).val+(boundaryImPowerRow77_10Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_9Degree19Norm x).property (boundaryImPowerRow77_10Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_9Degree19Norm,boundaryImPowerRow77_10Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block29Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))))=(boundaryImPowerRow77_8Degree19Norm x).val+(boundaryFullPowerDegree19Block28Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_8Degree19Norm x).property (boundaryFullPowerDegree19Block28Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_8Degree19Norm,boundaryFullPowerDegree19Block28Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block30Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))))))=(boundaryFullPowerDegree19Block27Norm x).val+(boundaryFullPowerDegree19Block29Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block27Norm x).property (boundaryFullPowerDegree19Block29Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block27Norm,boundaryFullPowerDegree19Block29Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block31Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x))))))))=(boundaryFullPowerDegree19Block25Norm x).val+(boundaryFullPowerDegree19Block30Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block25Norm x).property (boundaryFullPowerDegree19Block30Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block25Norm,boundaryFullPowerDegree19Block30Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block32Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x))=c} := by

  have he : ((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x))=(boundaryImPowerRow77_12Degree19Norm x).val+(boundaryImPowerRow77_13Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_12Degree19Norm x).property (boundaryImPowerRow77_13Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_12Degree19Norm,boundaryImPowerRow77_13Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block33Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x))))=(boundaryImPowerRow77_11Degree19Norm x).val+(boundaryFullPowerDegree19Block32Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_11Degree19Norm x).property (boundaryFullPowerDegree19Block32Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_11Degree19Norm,boundaryFullPowerDegree19Block32Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block34Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x))=c} := by

  have he : ((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x))=(boundaryImPowerRow77_15Degree19Norm x).val+(boundaryImPowerRow77_16Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_15Degree19Norm x).property (boundaryImPowerRow77_16Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_15Degree19Norm,boundaryImPowerRow77_16Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block35Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x))))=(boundaryImPowerRow77_14Degree19Norm x).val+(boundaryFullPowerDegree19Block34Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_14Degree19Norm x).property (boundaryFullPowerDegree19Block34Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_14Degree19Norm,boundaryFullPowerDegree19Block34Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block36Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x))))))=(boundaryFullPowerDegree19Block33Norm x).val+(boundaryFullPowerDegree19Block35Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block33Norm x).property (boundaryFullPowerDegree19Block35Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block33Norm,boundaryFullPowerDegree19Block35Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block37Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x))=c} := by

  have he : ((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x))=(boundaryImPowerRow77_18Degree19Norm x).val+(boundaryImPowerRow77_19Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_18Degree19Norm x).property (boundaryImPowerRow77_19Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_18Degree19Norm,boundaryImPowerRow77_19Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block38Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x))))=(boundaryImPowerRow77_17Degree19Norm x).val+(boundaryFullPowerDegree19Block37Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_17Degree19Norm x).property (boundaryFullPowerDegree19Block37Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_17Degree19Norm,boundaryFullPowerDegree19Block37Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block39Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))=c} := by

  have he : ((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))=(boundaryImPowerRow77_21Degree19Norm x).val+(boundaryLowPowerRow77Degree19Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_21Degree19Norm x).property (boundaryLowPowerRow77Degree19Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_21Degree19Norm,boundaryLowPowerRow77Degree19Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block40Norm (x : ℕ → ℝ) : {c : ℝ // ((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))=c} := by

  have he : ((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))=(boundaryImPowerRow77_20Degree19Norm x).val+(boundaryFullPowerDegree19Block39Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryImPowerRow77_20Degree19Norm x).property (boundaryFullPowerDegree19Block39Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryImPowerRow77_20Degree19Norm,boundaryFullPowerDegree19Block39Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block41Norm (x : ℕ → ℝ) : {c : ℝ // ((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))=c} := by

  have he : ((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))=(boundaryFullPowerDegree19Block38Norm x).val+(boundaryFullPowerDegree19Block40Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block38Norm x).property (boundaryFullPowerDegree19Block40Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block38Norm,boundaryFullPowerDegree19Block40Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block42Norm (x : ℕ → ℝ) : {c : ℝ // ((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))))=c} := by

  have he : ((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))))=(boundaryFullPowerDegree19Block36Norm x).val+(boundaryFullPowerDegree19Block41Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block36Norm x).property (boundaryFullPowerDegree19Block41Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block36Norm,boundaryFullPowerDegree19Block41Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block43Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x)))))))))+(((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))))))=c} := by

  have he : ((((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x)))))))))+(((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))))))=(boundaryFullPowerDegree19Block31Norm x).val+(boundaryFullPowerDegree19Block42Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block31Norm x).property (boundaryFullPowerDegree19Block42Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block31Norm,boundaryFullPowerDegree19Block42Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerDegree19Block44Norm (x : ℕ → ℝ) : {c : ℝ // ((((((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x)))))))))+(((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x)))))))))))+(((((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x)))))))))+(((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))))))))=c} := by

  have he : ((((((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x)))))))))+(((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x)))))))))))+(((((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x)))))))))+(((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x))))))))))))=(boundaryFullPowerDegree19Block21Norm x).val+(boundaryFullPowerDegree19Block43Norm x).val :=

    congrArg₂ (fun a b : ℝ => a+b) (boundaryFullPowerDegree19Block21Norm x).property (boundaryFullPowerDegree19Block43Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block21Norm,boundaryFullPowerDegree19Block43Norm]

    try ring_nf

  exact ⟨_,he⟩

def boundaryFullPowerRow77Degree19Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 19 x=c} := by

  have he0 : boundaryFullPowerRow77 19 x=((((((((((boundaryRePowerRow77_0 19 x)+(boundaryRePowerRow77_1 19 x)))+(((boundaryRePowerRow77_2 19 x)+(((boundaryRePowerRow77_3 19 x)+(boundaryRePowerRow77_4 19 x)))))))+(((((boundaryRePowerRow77_5 19 x)+(((boundaryRePowerRow77_6 19 x)+(boundaryRePowerRow77_7 19 x)))))+(((boundaryRePowerRow77_8 19 x)+(((boundaryRePowerRow77_9 19 x)+(boundaryRePowerRow77_10 19 x)))))))))+(((((((boundaryRePowerRow77_11 19 x)+(((boundaryRePowerRow77_12 19 x)+(boundaryRePowerRow77_13 19 x)))))+(((boundaryRePowerRow77_14 19 x)+(((boundaryRePowerRow77_15 19 x)+(boundaryRePowerRow77_16 19 x)))))))+(((((boundaryRePowerRow77_17 19 x)+(((boundaryRePowerRow77_18 19 x)+(boundaryRePowerRow77_19 19 x)))))+(((boundaryRePowerRow77_20 19 x)+(((boundaryRePowerRow77_21 19 x)+(boundaryRePowerRow77_22 19 x)))))))))))+(((((((((boundaryImPowerRow77_0 19 x)+(boundaryImPowerRow77_1 19 x)))+(((boundaryImPowerRow77_2 19 x)+(((boundaryImPowerRow77_3 19 x)+(boundaryImPowerRow77_4 19 x)))))))+(((((boundaryImPowerRow77_5 19 x)+(((boundaryImPowerRow77_6 19 x)+(boundaryImPowerRow77_7 19 x)))))+(((boundaryImPowerRow77_8 19 x)+(((boundaryImPowerRow77_9 19 x)+(boundaryImPowerRow77_10 19 x)))))))))+(((((((boundaryImPowerRow77_11 19 x)+(((boundaryImPowerRow77_12 19 x)+(boundaryImPowerRow77_13 19 x)))))+(((boundaryImPowerRow77_14 19 x)+(((boundaryImPowerRow77_15 19 x)+(boundaryImPowerRow77_16 19 x)))))))+(((((boundaryImPowerRow77_17 19 x)+(((boundaryImPowerRow77_18 19 x)+(boundaryImPowerRow77_19 19 x)))))+(((boundaryImPowerRow77_20 19 x)+(((boundaryImPowerRow77_21 19 x)+(boundaryLowPowerRow77 19 x)))))))))))) := by

    dsimp only [boundaryFullPowerRow77]

    try ac_rfl

  have he := he0.trans (boundaryFullPowerDegree19Block44Norm x).property

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerDegree19Block44Norm]

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
