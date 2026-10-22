import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CoefficientFull

import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CoefficientSupport

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryLowCoefficient77Row3Norm (B : ℕ) : {c : ℝ // boundaryLowCoefficient77 3 B=c} := by

  have he : boundaryLowCoefficient77 3 B=boundaryLowCoefficient77 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryLowCoefficient77]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_0Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_0 3 B=c} := by

  have he : boundaryReCoefficient77_0 3 B=boundaryReCoefficient77_0 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_0]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_1Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_1 3 B=c} := by

  have he : boundaryReCoefficient77_1 3 B=boundaryReCoefficient77_1 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_1]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_2Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_2 3 B=c} := by

  have he : boundaryReCoefficient77_2 3 B=boundaryReCoefficient77_2 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_2]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_3Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_3 3 B=c} := by

  have he : boundaryReCoefficient77_3 3 B=boundaryReCoefficient77_3 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_3]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_4Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_4 3 B=c} := by

  have he : boundaryReCoefficient77_4 3 B=boundaryReCoefficient77_4 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_4]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_5Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_5 3 B=c} := by

  have he : boundaryReCoefficient77_5 3 B=boundaryReCoefficient77_5 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_5]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_6Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_6 3 B=c} := by

  have he : boundaryReCoefficient77_6 3 B=boundaryReCoefficient77_6 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_6]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_7Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_7 3 B=c} := by

  have he : boundaryReCoefficient77_7 3 B=boundaryReCoefficient77_7 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_7]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_8Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_8 3 B=c} := by

  have he : boundaryReCoefficient77_8 3 B=boundaryReCoefficient77_8 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_8]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_9Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_9 3 B=c} := by

  have he : boundaryReCoefficient77_9 3 B=boundaryReCoefficient77_9 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_9]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_10Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_10 3 B=c} := by

  have he : boundaryReCoefficient77_10 3 B=boundaryReCoefficient77_10 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_10]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_11Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_11 3 B=c} := by

  have he : boundaryReCoefficient77_11 3 B=boundaryReCoefficient77_11 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_11]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_12Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_12 3 B=c} := by

  have he : boundaryReCoefficient77_12 3 B=boundaryReCoefficient77_12 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_12]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_13Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_13 3 B=c} := by

  have he : boundaryReCoefficient77_13 3 B=boundaryReCoefficient77_13 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_13]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_14Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_14 3 B=c} := by

  have he : boundaryReCoefficient77_14 3 B=boundaryReCoefficient77_14 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_14]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_15Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_15 3 B=c} := by

  have he : boundaryReCoefficient77_15 3 B=boundaryReCoefficient77_15 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_15]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_16Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_16 3 B=c} := by

  have he : boundaryReCoefficient77_16 3 B=boundaryReCoefficient77_16 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_16]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_17Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_17 3 B=c} := by

  have he : boundaryReCoefficient77_17 3 B=boundaryReCoefficient77_17 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_17]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_18Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_18 3 B=c} := by

  have he : boundaryReCoefficient77_18 3 B=boundaryReCoefficient77_18 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_18]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_19Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_19 3 B=c} := by

  have he : boundaryReCoefficient77_19 3 B=boundaryReCoefficient77_19 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_19]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_20Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_20 3 B=c} := by

  have he : boundaryReCoefficient77_20 3 B=boundaryReCoefficient77_20 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_20]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_21Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_21 3 B=c} := by

  have he : boundaryReCoefficient77_21 3 B=boundaryReCoefficient77_21 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_21]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryReCoefficient77_22Row3Norm (B : ℕ) : {c : ℝ // boundaryReCoefficient77_22 3 B=c} := by

  have he : boundaryReCoefficient77_22 3 B=boundaryReCoefficient77_22 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryReCoefficient77_22]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_0Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_0 3 B=c} := by

  have he : boundaryImCoefficient77_0 3 B=boundaryImCoefficient77_0 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_0]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_1Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_1 3 B=c} := by

  have he : boundaryImCoefficient77_1 3 B=boundaryImCoefficient77_1 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_1]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_2Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_2 3 B=c} := by

  have he : boundaryImCoefficient77_2 3 B=boundaryImCoefficient77_2 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_2]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_3Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_3 3 B=c} := by

  have he : boundaryImCoefficient77_3 3 B=boundaryImCoefficient77_3 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_3]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_4Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_4 3 B=c} := by

  have he : boundaryImCoefficient77_4 3 B=boundaryImCoefficient77_4 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_4]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_5Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_5 3 B=c} := by

  have he : boundaryImCoefficient77_5 3 B=boundaryImCoefficient77_5 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_5]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_6Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_6 3 B=c} := by

  have he : boundaryImCoefficient77_6 3 B=boundaryImCoefficient77_6 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_6]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_7Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_7 3 B=c} := by

  have he : boundaryImCoefficient77_7 3 B=boundaryImCoefficient77_7 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_7]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_8Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_8 3 B=c} := by

  have he : boundaryImCoefficient77_8 3 B=boundaryImCoefficient77_8 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_8]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_9Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_9 3 B=c} := by

  have he : boundaryImCoefficient77_9 3 B=boundaryImCoefficient77_9 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_9]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_10Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_10 3 B=c} := by

  have he : boundaryImCoefficient77_10 3 B=boundaryImCoefficient77_10 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_10]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_11Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_11 3 B=c} := by

  have he : boundaryImCoefficient77_11 3 B=boundaryImCoefficient77_11 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_11]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_12Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_12 3 B=c} := by

  have he : boundaryImCoefficient77_12 3 B=boundaryImCoefficient77_12 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_12]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_13Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_13 3 B=c} := by

  have he : boundaryImCoefficient77_13 3 B=boundaryImCoefficient77_13 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_13]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_14Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_14 3 B=c} := by

  have he : boundaryImCoefficient77_14 3 B=boundaryImCoefficient77_14 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_14]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_15Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_15 3 B=c} := by

  have he : boundaryImCoefficient77_15 3 B=boundaryImCoefficient77_15 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_15]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_16Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_16 3 B=c} := by

  have he : boundaryImCoefficient77_16 3 B=boundaryImCoefficient77_16 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_16]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_17Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_17 3 B=c} := by

  have he : boundaryImCoefficient77_17 3 B=boundaryImCoefficient77_17 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_17]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_18Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_18 3 B=c} := by

  have he : boundaryImCoefficient77_18 3 B=boundaryImCoefficient77_18 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_18]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_19Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_19 3 B=c} := by

  have he : boundaryImCoefficient77_19 3 B=boundaryImCoefficient77_19 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_19]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_20Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_20 3 B=c} := by

  have he : boundaryImCoefficient77_20 3 B=boundaryImCoefficient77_20 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_20]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


def boundaryImCoefficient77_21Row3Norm (B : ℕ) : {c : ℝ // boundaryImCoefficient77_21 3 B=c} := by

  have he : boundaryImCoefficient77_21 3 B=boundaryImCoefficient77_21 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryImCoefficient77_21]

    simp (disch := omega) only [boundaryTermCoefficient77_zero_clock]

    norm_num [boundaryTermCoefficient77,boundaryTermScalar77,boundaryH77,boundaryS77,Finset.sum_range_succ,degreeElevationCoefficient]

    try ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


end

end HTGeometry.ThetaRatioInfinity
