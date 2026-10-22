import GaloisForLFunctions.HTGeometry.PolynomialODE.JetClosure

/-!
# Orders of the coupled seam-jet recursion

The reflected modular seam jets satisfy one fixed coupled recursion in the
binomial convolution. Its orders are rational in the two seam parameters `M`
and `R`: `h` is linear in `M`, and `z`, `r`, `p` are independent of `M`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- The coupled seam recursion satisfied by the reflected modular source jets:
initial data at order zero and one convolution step for each component. -/
structure SeamJetSystem (M R : ℂ) (h z r p : ℕ → ℂ) : Prop where
  h_zero : h 0 = M
  z_zero : z 0 = 0
  r_zero : r 0 = R
  p_zero : p 0 = 0
  h_succ : ∀ n, h (n + 1) =
    -(1 / 6 : ℂ) *
      scalarJetConvolution h
        (fun k => p k + scalarJetConvolution r z k) n
  z_succ : ∀ n, z (n + 1) =
    -scalarJetConvolution r
      (fun k => scalarJetUnit k - scalarJetConvolution z z k) n
  r_succ : ∀ n, r (n + 1) =
    -(2 / 3 : ℂ) *
      scalarJetConvolution r
        (fun k => p k + scalarJetConvolution r z k) n
  p_succ : ∀ n, p (n + 1) =
    3 * scalarJetUnit n -
      (1 / 3 : ℂ) * scalarJetConvolution p p n +
      (1 / 12 : ℂ) *
        scalarJetConvolution (scalarJetConvolution r r)
          (fun k => 3 * scalarJetUnit k +
            scalarJetConvolution z z k) n

/-- Order 1 of the coupled seam recursion: the `h` component. -/
theorem seamJetH1 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 1 = 0 := by
  have e := J.h_succ 0
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero
    ] at e
  rw [e]
  try ring

/-- Order 1 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ1 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 1 = (-1 : ℂ)*R^(1 : ℕ) := by
  have e := J.z_succ 0
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero
    ] at e
  rw [e]
  try ring

/-- Order 1 of the coupled seam recursion: the `r` component. -/
theorem seamJetR1 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 1 = 0 := by
  have e := J.r_succ 0
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero
    ] at e
  rw [e]
  try ring

/-- Order 1 of the coupled seam recursion: the `p` component. -/
theorem seamJetP1 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 1 = (3 : ℂ) + (1 / 4 : ℂ)*R^(2 : ℕ) := by
  have e := J.p_succ 0
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero
    ] at e
  rw [e]
  try ring

/-- All four components at order 1. -/
theorem seamJetOrder1 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 1 = 0 ∧ z 1 = (-1 : ℂ)*R^(1 : ℕ) ∧
      r 1 = 0 ∧ p 1 = (3 : ℂ) + (1 / 4 : ℂ)*R^(2 : ℕ) :=
  ⟨seamJetH1 J, seamJetZ1 J, seamJetR1 J, seamJetP1 J⟩

/-- Order 2 of the coupled seam recursion: the `h` component. -/
theorem seamJetH2 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 2 = (-1 / 2 : ℂ)*M^(1 : ℕ) + (1 / 8 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) := by
  have e := J.h_succ 1
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J] at e
  rw [e]
  try ring

/-- Order 2 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ2 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 2 = 0 := by
  have e := J.z_succ 1
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J] at e
  rw [e]
  try ring

/-- Order 2 of the coupled seam recursion: the `r` component. -/
theorem seamJetR2 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 2 = (-2 : ℂ)*R^(1 : ℕ) + (1 / 2 : ℂ)*R^(3 : ℕ) := by
  have e := J.r_succ 1
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J] at e
  rw [e]
  try ring

/-- Order 2 of the coupled seam recursion: the `p` component. -/
theorem seamJetP2 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 2 = 0 := by
  have e := J.p_succ 1
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J] at e
  rw [e]
  try ring

/-- All four components at order 2. -/
theorem seamJetOrder2 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 2 = (-1 / 2 : ℂ)*M^(1 : ℕ) + (1 / 8 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) ∧ z 2 = 0 ∧
      r 2 = (-2 : ℂ)*R^(1 : ℕ) + (1 / 2 : ℂ)*R^(3 : ℕ) ∧ p 2 = 0 :=
  ⟨seamJetH2 J, seamJetZ2 J, seamJetR2 J, seamJetP2 J⟩

/-- Order 3 of the coupled seam recursion: the `h` component. -/
theorem seamJetH3 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 3 = 0 := by
  have e := J.h_succ 2
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J] at e
  rw [e]
  try ring

/-- Order 3 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ3 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 3 = (2 : ℂ)*R^(1 : ℕ) + (3 / 2 : ℂ)*R^(3 : ℕ) := by
  have e := J.z_succ 2
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J] at e
  rw [e]
  try ring

/-- Order 3 of the coupled seam recursion: the `r` component. -/
theorem seamJetR3 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 3 = 0 := by
  have e := J.r_succ 2
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J] at e
  rw [e]
  try ring

/-- Order 3 of the coupled seam recursion: the `p` component. -/
theorem seamJetP3 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 3 = (-6 : ℂ) + (-2 : ℂ)*R^(2 : ℕ) + (3 / 8 : ℂ)*R^(4 : ℕ) := by
  have e := J.p_succ 2
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J] at e
  rw [e]
  try ring

/-- All four components at order 3. -/
theorem seamJetOrder3 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 3 = 0 ∧ z 3 = (2 : ℂ)*R^(1 : ℕ) + (3 / 2 : ℂ)*R^(3 : ℕ) ∧
      r 3 = 0 ∧ p 3 = (-6 : ℂ) + (-2 : ℂ)*R^(2 : ℕ) + (3 / 8 : ℂ)*R^(4 : ℕ) :=
  ⟨seamJetH3 J, seamJetZ3 J, seamJetR3 J, seamJetP3 J⟩

/-- Order 4 of the coupled seam recursion: the `h` component. -/
theorem seamJetH4 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 4 = (7 / 4 : ℂ)*M^(1 : ℕ) + (-11 / 8 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (-1 / 64 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) := by
  have e := J.h_succ 3
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J] at e
  rw [e]
  try ring

/-- Order 4 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ4 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 4 = 0 := by
  have e := J.z_succ 3
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J] at e
  rw [e]
  try ring

/-- Order 4 of the coupled seam recursion: the `r` component. -/
theorem seamJetR4 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 4 = (16 : ℂ)*R^(1 : ℕ) + (-10 : ℂ)*R^(3 : ℕ) + (1 / 2 : ℂ)*R^(5 : ℕ) := by
  have e := J.r_succ 3
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J] at e
  rw [e]
  try ring

/-- Order 4 of the coupled seam recursion: the `p` component. -/
theorem seamJetP4 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 4 = 0 := by
  have e := J.p_succ 3
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J] at e
  rw [e]
  try ring

/-- All four components at order 4. -/
theorem seamJetOrder4 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 4 = (7 / 4 : ℂ)*M^(1 : ℕ) + (-11 / 8 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (-1 / 64 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) ∧ z 4 = 0 ∧
      r 4 = (16 : ℂ)*R^(1 : ℕ) + (-10 : ℂ)*R^(3 : ℕ) + (1 / 2 : ℂ)*R^(5 : ℕ) ∧ p 4 = 0 :=
  ⟨seamJetH4 J, seamJetZ4 J, seamJetR4 J, seamJetP4 J⟩

/-- Order 5 of the coupled seam recursion: the `h` component. -/
theorem seamJetH5 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 5 = 0 := by
  have e := J.h_succ 4
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J] at e
  rw [e]
  try ring

/-- Order 5 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ5 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 5 = (-16 : ℂ)*R^(1 : ℕ) + (-30 : ℂ)*R^(3 : ℕ) + (-13 / 2 : ℂ)*R^(5 : ℕ) := by
  have e := J.z_succ 4
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J] at e
  rw [e]
  try ring

/-- Order 5 of the coupled seam recursion: the `r` component. -/
theorem seamJetR5 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 5 = 0 := by
  have e := J.r_succ 4
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J] at e
  rw [e]
  try ring

/-- Order 5 of the coupled seam recursion: the `p` component. -/
theorem seamJetP5 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 5 = (48 : ℂ) + (34 : ℂ)*R^(2 : ℕ) + (-15 : ℂ)*R^(4 : ℕ) + (3 / 8 : ℂ)*R^(6 : ℕ) := by
  have e := J.p_succ 4
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J] at e
  rw [e]
  try ring

/-- All four components at order 5. -/
theorem seamJetOrder5 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 5 = 0 ∧ z 5 = (-16 : ℂ)*R^(1 : ℕ) + (-30 : ℂ)*R^(3 : ℕ) + (-13 / 2 : ℂ)*R^(5 : ℕ) ∧
      r 5 = 0 ∧ p 5 = (48 : ℂ) + (34 : ℂ)*R^(2 : ℕ) + (-15 : ℂ)*R^(4 : ℕ) + (3 / 8 : ℂ)*R^(6 : ℕ) :=
  ⟨seamJetH5 J, seamJetZ5 J, seamJetR5 J, seamJetP5 J⟩

/-- Order 6 of the coupled seam recursion: the `h` component. -/
theorem seamJetH6 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 6 = (-139 / 8 : ℂ)*M^(1 : ℕ) + (889 / 32 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (95 / 128 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (51 / 512 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) := by
  have e := J.h_succ 5
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J] at e
  rw [e]
  try ring

/-- Order 6 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ6 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 6 = 0 := by
  have e := J.z_succ 5
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J] at e
  rw [e]
  try ring

/-- Order 6 of the coupled seam recursion: the `r` component. -/
theorem seamJetR6 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 6 = (-272 : ℂ)*R^(1 : ℕ) + (308 : ℂ)*R^(3 : ℕ) + (-35 : ℂ)*R^(5 : ℕ) + (3 / 4 : ℂ)*R^(7 : ℕ) := by
  have e := J.r_succ 5
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J] at e
  rw [e]
  try ring

/-- Order 6 of the coupled seam recursion: the `p` component. -/
theorem seamJetP6 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 6 = 0 := by
  have e := J.p_succ 5
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J] at e
  rw [e]
  try ring

/-- All four components at order 6. -/
theorem seamJetOrder6 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 6 = (-139 / 8 : ℂ)*M^(1 : ℕ) + (889 / 32 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (95 / 128 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (51 / 512 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) ∧ z 6 = 0 ∧
      r 6 = (-272 : ℂ)*R^(1 : ℕ) + (308 : ℂ)*R^(3 : ℕ) + (-35 : ℂ)*R^(5 : ℕ) + (3 / 4 : ℂ)*R^(7 : ℕ) ∧ p 6 = 0 :=
  ⟨seamJetH6 J, seamJetZ6 J, seamJetR6 J, seamJetP6 J⟩

/-- Order 7 of the coupled seam recursion: the `h` component. -/
theorem seamJetH7 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 7 = 0 := by
  have e := J.h_succ 6
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J] at e
  rw [e]
  try ring

/-- Order 7 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ7 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 7 = (272 : ℂ)*R^(1 : ℕ) + (924 : ℂ)*R^(3 : ℕ) + (455 : ℂ)*R^(5 : ℕ) + (189 / 4 : ℂ)*R^(7 : ℕ) := by
  have e := J.z_succ 6
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J] at e
  rw [e]
  try ring

/-- Order 7 of the coupled seam recursion: the `r` component. -/
theorem seamJetR7 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 7 = 0 := by
  have e := J.r_succ 6
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J] at e
  rw [e]
  try ring

/-- Order 7 of the coupled seam recursion: the `p` component. -/
theorem seamJetP7 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 7 = (-816 : ℂ) + (-992 : ℂ)*R^(2 : ℕ) + (756 : ℂ)*R^(4 : ℕ) + (-42 : ℂ)*R^(6 : ℕ) + (39 / 16 : ℂ)*R^(8 : ℕ) := by
  have e := J.p_succ 6
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J] at e
  rw [e]
  try ring

/-- All four components at order 7. -/
theorem seamJetOrder7 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 7 = 0 ∧ z 7 = (272 : ℂ)*R^(1 : ℕ) + (924 : ℂ)*R^(3 : ℕ) + (455 : ℂ)*R^(5 : ℕ) + (189 / 4 : ℂ)*R^(7 : ℕ) ∧
      r 7 = 0 ∧ p 7 = (-816 : ℂ) + (-992 : ℂ)*R^(2 : ℕ) + (756 : ℂ)*R^(4 : ℕ) + (-42 : ℂ)*R^(6 : ℕ) + (39 / 16 : ℂ)*R^(8 : ℕ) :=
  ⟨seamJetH7 J, seamJetZ7 J, seamJetR7 J, seamJetP7 J⟩

/-- Order 8 of the coupled seam recursion: the `h` component. -/
theorem seamJetH8 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 8 = (5473 / 16 : ℂ)*M^(1 : ℕ) + (-14677 / 16 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (-5397 / 128 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (-3213 / 256 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (849 / 4096 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) := by
  have e := J.h_succ 7
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J] at e
  rw [e]
  try ring

/-- Order 8 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ8 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 8 = 0 := by
  have e := J.z_succ 7
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J] at e
  rw [e]
  try ring

/-- Order 8 of the coupled seam recursion: the `r` component. -/
theorem seamJetR8 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 8 = (7936 : ℂ)*R^(1 : ℕ) + (-14080 : ℂ)*R^(3 : ℕ) + (2688 : ℂ)*R^(5 : ℕ) + (-126 : ℂ)*R^(7 : ℕ) + (9 / 2 : ℂ)*R^(9 : ℕ) := by
  have e := J.r_succ 7
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J] at e
  rw [e]
  try ring

/-- Order 8 of the coupled seam recursion: the `p` component. -/
theorem seamJetP8 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 8 = 0 := by
  have e := J.p_succ 7
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J] at e
  rw [e]
  try ring

/-- All four components at order 8. -/
theorem seamJetOrder8 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 8 = (5473 / 16 : ℂ)*M^(1 : ℕ) + (-14677 / 16 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (-5397 / 128 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (-3213 / 256 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (849 / 4096 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) ∧ z 8 = 0 ∧
      r 8 = (7936 : ℂ)*R^(1 : ℕ) + (-14080 : ℂ)*R^(3 : ℕ) + (2688 : ℂ)*R^(5 : ℕ) + (-126 : ℂ)*R^(7 : ℕ) + (9 / 2 : ℂ)*R^(9 : ℕ) ∧ p 8 = 0 :=
  ⟨seamJetH8 J, seamJetZ8 J, seamJetR8 J, seamJetP8 J⟩

/-- Order 9 of the coupled seam recursion: the `h` component. -/
theorem seamJetH9 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 9 = 0 := by
  have e := J.h_succ 8
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J] at e
  rw [e]
  try ring

/-- Order 9 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ9 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 9 = (-7936 : ℂ)*R^(1 : ℕ) + (-42240 : ℂ)*R^(3 : ℕ) + (-34944 : ℂ)*R^(5 : ℕ) + (-7938 : ℂ)*R^(7 : ℕ) + (-1017 / 2 : ℂ)*R^(9 : ℕ) := by
  have e := J.z_succ 8
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J] at e
  rw [e]
  try ring

/-- Order 9 of the coupled seam recursion: the `r` component. -/
theorem seamJetR9 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 9 = 0 := by
  have e := J.r_succ 8
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J] at e
  rw [e]
  try ring

/-- Order 9 of the coupled seam recursion: the `p` component. -/
theorem seamJetP9 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 9 = (23808 : ℂ) + (44224 : ℂ)*R^(2 : ℕ) + (-50880 : ℂ)*R^(4 : ℕ) + (4662 : ℂ)*R^(6 : ℕ) + (-585 : ℂ)*R^(8 : ℕ) + (27 / 8 : ℂ)*R^(10 : ℕ) := by
  have e := J.p_succ 8
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J] at e
  rw [e]
  try ring

/-- All four components at order 9. -/
theorem seamJetOrder9 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 9 = 0 ∧ z 9 = (-7936 : ℂ)*R^(1 : ℕ) + (-42240 : ℂ)*R^(3 : ℕ) + (-34944 : ℂ)*R^(5 : ℕ) + (-7938 : ℂ)*R^(7 : ℕ) + (-1017 / 2 : ℂ)*R^(9 : ℕ) ∧
      r 9 = 0 ∧ p 9 = (23808 : ℂ) + (44224 : ℂ)*R^(2 : ℕ) + (-50880 : ℂ)*R^(4 : ℕ) + (4662 : ℂ)*R^(6 : ℕ) + (-585 : ℂ)*R^(8 : ℕ) + (27 / 8 : ℂ)*R^(10 : ℕ) :=
  ⟨seamJetH9 J, seamJetZ9 J, seamJetR9 J, seamJetP9 J⟩

/-- Order 10 of the coupled seam recursion: the `h` component. -/
theorem seamJetH10 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 10 = (-357721 / 32 : ℂ)*M^(1 : ℕ) + (5771821 / 128 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (797555 / 256 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (1562589 / 1024 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (-445725 / 8192 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) + (-26199 / 32768 : ℂ)*M^(1 : ℕ)*R^(10 : ℕ) := by
  have e := J.h_succ 9
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J] at e
  rw [e]
  try ring

/-- Order 10 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ10 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 10 = 0 := by
  have e := J.z_succ 9
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J] at e
  rw [e]
  try ring

/-- Order 10 of the coupled seam recursion: the `r` component. -/
theorem seamJetR10 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 10 = (-353792 : ℂ)*R^(1 : ℕ) + (902528 : ℂ)*R^(3 : ℕ) + (-254320 : ℂ)*R^(5 : ℕ) + (19404 : ℂ)*R^(7 : ℕ) + (-1485 : ℂ)*R^(9 : ℕ) + (117 / 4 : ℂ)*R^(11 : ℕ) := by
  have e := J.r_succ 9
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J] at e
  rw [e]
  try ring

/-- Order 10 of the coupled seam recursion: the `p` component. -/
theorem seamJetP10 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 10 = 0 := by
  have e := J.p_succ 9
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J] at e
  rw [e]
  try ring

/-- All four components at order 10. -/
theorem seamJetOrder10 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 10 = (-357721 / 32 : ℂ)*M^(1 : ℕ) + (5771821 / 128 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (797555 / 256 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (1562589 / 1024 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (-445725 / 8192 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) + (-26199 / 32768 : ℂ)*M^(1 : ℕ)*R^(10 : ℕ) ∧ z 10 = 0 ∧
      r 10 = (-353792 : ℂ)*R^(1 : ℕ) + (902528 : ℂ)*R^(3 : ℕ) + (-254320 : ℂ)*R^(5 : ℕ) + (19404 : ℂ)*R^(7 : ℕ) + (-1485 : ℂ)*R^(9 : ℕ) + (117 / 4 : ℂ)*R^(11 : ℕ) ∧ p 10 = 0 :=
  ⟨seamJetH10 J, seamJetZ10 J, seamJetR10 J, seamJetP10 J⟩

/-- Order 11 of the coupled seam recursion: the `h` component. -/
theorem seamJetH11 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 11 = 0 := by
  have e := J.h_succ 10
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J] at e
  rw [e]
  try ring

/-- Order 11 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ11 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 11 = (353792 : ℂ)*R^(1 : ℕ) + (2707584 : ℂ)*R^(3 : ℕ) + (3306160 : ℂ)*R^(5 : ℕ) + (1222452 : ℂ)*R^(7 : ℕ) + (167805 : ℂ)*R^(9 : ℕ) + (30591 / 4 : ℂ)*R^(11 : ℕ) := by
  have e := J.z_succ 10
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J] at e
  rw [e]
  try ring

/-- Order 11 of the coupled seam recursion: the `r` component. -/
theorem seamJetR11 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 11 = 0 := by
  have e := J.r_succ 10
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J] at e
  rw [e]
  try ring

/-- Order 11 of the coupled seam recursion: the `p` component. -/
theorem seamJetP11 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 11 = (-1061376 : ℂ) + (-2796032 : ℂ)*R^(2 : ℕ) + (4491696 : ℂ)*R^(4 : ℕ) + (-598224 : ℂ)*R^(6 : ℕ) + (120978 : ℂ)*R^(8 : ℕ) + (-1485 : ℂ)*R^(10 : ℕ) + (1341 / 16 : ℂ)*R^(12 : ℕ) := by
  have e := J.p_succ 10
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J] at e
  rw [e]
  try ring

/-- All four components at order 11. -/
theorem seamJetOrder11 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 11 = 0 ∧ z 11 = (353792 : ℂ)*R^(1 : ℕ) + (2707584 : ℂ)*R^(3 : ℕ) + (3306160 : ℂ)*R^(5 : ℕ) + (1222452 : ℂ)*R^(7 : ℕ) + (167805 : ℂ)*R^(9 : ℕ) + (30591 / 4 : ℂ)*R^(11 : ℕ) ∧
      r 11 = 0 ∧ p 11 = (-1061376 : ℂ) + (-2796032 : ℂ)*R^(2 : ℕ) + (4491696 : ℂ)*R^(4 : ℕ) + (-598224 : ℂ)*R^(6 : ℕ) + (120978 : ℂ)*R^(8 : ℕ) + (-1485 : ℂ)*R^(10 : ℕ) + (1341 / 16 : ℂ)*R^(12 : ℕ) :=
  ⟨seamJetH11 J, seamJetZ11 J, seamJetR11 J, seamJetP11 J⟩

/-- Order 12 of the coupled seam recursion: the `h` component. -/
theorem seamJetH12 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 12 = (34988647 / 64 : ℂ)*M^(1 : ℕ) + (-395756081 / 128 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (-304210511 / 1024 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (-216096639 / 1024 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (198388377 / 16384 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) + (12392127 / 32768 : ℂ)*M^(1 : ℕ)*R^(10 : ℕ) + (1341999 / 262144 : ℂ)*M^(1 : ℕ)*R^(12 : ℕ) := by
  have e := J.h_succ 11
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J] at e
  rw [e]
  try ring

/-- Order 12 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ12 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 12 = 0 := by
  have e := J.z_succ 11
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J] at e
  rw [e]
  try ring

/-- Order 12 of the coupled seam recursion: the `r` component. -/
theorem seamJetR12 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 12 = (22368256 : ℂ)*R^(1 : ℕ) + (-77459200 : ℂ)*R^(3 : ℕ) + (29917888 : ℂ)*R^(5 : ℕ) + (-3280992 : ℂ)*R^(7 : ℕ) + (401544 : ℂ)*R^(9 : ℕ) + (-16731 : ℂ)*R^(11 : ℕ) + (387 / 4 : ℂ)*R^(13 : ℕ) := by
  have e := J.r_succ 11
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J] at e
  rw [e]
  try ring

/-- Order 12 of the coupled seam recursion: the `p` component. -/
theorem seamJetP12 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 12 = 0 := by
  have e := J.p_succ 11
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J] at e
  rw [e]
  try ring

/-- All four components at order 12. -/
theorem seamJetOrder12 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 12 = (34988647 / 64 : ℂ)*M^(1 : ℕ) + (-395756081 / 128 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (-304210511 / 1024 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (-216096639 / 1024 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (198388377 / 16384 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) + (12392127 / 32768 : ℂ)*M^(1 : ℕ)*R^(10 : ℕ) + (1341999 / 262144 : ℂ)*M^(1 : ℕ)*R^(12 : ℕ) ∧ z 12 = 0 ∧
      r 12 = (22368256 : ℂ)*R^(1 : ℕ) + (-77459200 : ℂ)*R^(3 : ℕ) + (29917888 : ℂ)*R^(5 : ℕ) + (-3280992 : ℂ)*R^(7 : ℕ) + (401544 : ℂ)*R^(9 : ℕ) + (-16731 : ℂ)*R^(11 : ℕ) + (387 / 4 : ℂ)*R^(13 : ℕ) ∧ p 12 = 0 :=
  ⟨seamJetH12 J, seamJetZ12 J, seamJetR12 J, seamJetP12 J⟩

/-- Order 13 of the coupled seam recursion: the `h` component. -/
theorem seamJetH13 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 13 = 0 := by
  have e := J.h_succ 12
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J] at e
  rw [e]
  try ring

/-- Order 13 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ13 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 13 = (-22368256 : ℂ)*R^(1 : ℕ) + (-232377600 : ℂ)*R^(3 : ℕ) + (-388932544 : ℂ)*R^(5 : ℕ) + (-206702496 : ℂ)*R^(7 : ℕ) + (-45374472 : ℂ)*R^(9 : ℕ) + (-4374513 : ℂ)*R^(11 : ℕ) + (-609831 / 4 : ℂ)*R^(13 : ℕ) := by
  have e := J.z_succ 12
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J] at e
  rw [e]
  try ring

/-- Order 13 of the coupled seam recursion: the `r` component. -/
theorem seamJetR13 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 13 = 0 := by
  have e := J.r_succ 12
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J] at e
  rw [e]
  try ring

/-- Order 13 of the coupled seam recursion: the `p` component. -/
theorem seamJetP13 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 13 = (67104768 : ℂ) + (237969664 : ℂ)*R^(2 : ℕ) + (-506862720 : ℂ)*R^(4 : ℕ) + (91339248 : ℂ)*R^(6 : ℕ) + (-26323440 : ℂ)*R^(8 : ℕ) + (513513 : ℂ)*R^(10 : ℕ) + (-122031 / 2 : ℂ)*R^(12 : ℕ) + (6111 / 16 : ℂ)*R^(14 : ℕ) := by
  have e := J.p_succ 12
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J] at e
  rw [e]
  try ring

/-- All four components at order 13. -/
theorem seamJetOrder13 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 13 = 0 ∧ z 13 = (-22368256 : ℂ)*R^(1 : ℕ) + (-232377600 : ℂ)*R^(3 : ℕ) + (-388932544 : ℂ)*R^(5 : ℕ) + (-206702496 : ℂ)*R^(7 : ℕ) + (-45374472 : ℂ)*R^(9 : ℕ) + (-4374513 : ℂ)*R^(11 : ℕ) + (-609831 / 4 : ℂ)*R^(13 : ℕ) ∧
      r 13 = 0 ∧ p 13 = (67104768 : ℂ) + (237969664 : ℂ)*R^(2 : ℕ) + (-506862720 : ℂ)*R^(4 : ℕ) + (91339248 : ℂ)*R^(6 : ℕ) + (-26323440 : ℂ)*R^(8 : ℕ) + (513513 : ℂ)*R^(10 : ℕ) + (-122031 / 2 : ℂ)*R^(12 : ℕ) + (6111 / 16 : ℂ)*R^(14 : ℕ) :=
  ⟨seamJetH13 J, seamJetZ13 J, seamJetR13 J, seamJetP13 J⟩

/-- Order 14 of the coupled seam recursion: the `h` component. -/
theorem seamJetH14 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 14 = (-4784061619 / 128 : ℂ)*M^(1 : ℕ) + (144425158669 / 512 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (73336684785 / 2048 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (281360592513 / 8192 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (-91897207545 / 32768 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) + (-18226513305 / 131072 : ℂ)*M^(1 : ℕ)*R^(10 : ℕ) + (-2076072453 / 524288 : ℂ)*M^(1 : ℕ)*R^(12 : ℕ) + (82018251 / 2097152 : ℂ)*M^(1 : ℕ)*R^(14 : ℕ) := by
  have e := J.h_succ 13
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J,
    seamJetH13 J,
    seamJetZ13 J,
    seamJetR13 J,
    seamJetP13 J] at e
  rw [e]
  try ring

/-- Order 14 of the coupled seam recursion: the `z` component. -/
theorem seamJetZ14 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    z 14 = 0 := by
  have e := J.z_succ 13
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J,
    seamJetH13 J,
    seamJetZ13 J,
    seamJetR13 J,
    seamJetP13 J] at e
  rw [e]
  try ring

/-- Order 14 of the coupled seam recursion: the `r` component. -/
theorem seamJetR14 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    r 14 = (-1903757312 : ℂ)*R^(1 : ℕ) + (8585742848 : ℂ)*R^(3 : ℕ) + (-4329386880 : ℂ)*R^(5 : ℕ) + (636251616 : ℂ)*R^(7 : ℕ) + (-110218680 : ℂ)*R^(9 : ℕ) + (7261254 : ℂ)*R^(11 : ℕ) + (-176085 / 2 : ℂ)*R^(13 : ℕ) + (14301 / 8 : ℂ)*R^(15 : ℕ) := by
  have e := J.r_succ 13
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J,
    seamJetH13 J,
    seamJetZ13 J,
    seamJetR13 J,
    seamJetP13 J] at e
  rw [e]
  try ring

/-- Order 14 of the coupled seam recursion: the `p` component. -/
theorem seamJetP14 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    p 14 = 0 := by
  have e := J.p_succ 13
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    J.h_zero, J.z_zero, J.r_zero, J.p_zero,
    seamJetH1 J,
    seamJetZ1 J,
    seamJetR1 J,
    seamJetP1 J,
    seamJetH2 J,
    seamJetZ2 J,
    seamJetR2 J,
    seamJetP2 J,
    seamJetH3 J,
    seamJetZ3 J,
    seamJetR3 J,
    seamJetP3 J,
    seamJetH4 J,
    seamJetZ4 J,
    seamJetR4 J,
    seamJetP4 J,
    seamJetH5 J,
    seamJetZ5 J,
    seamJetR5 J,
    seamJetP5 J,
    seamJetH6 J,
    seamJetZ6 J,
    seamJetR6 J,
    seamJetP6 J,
    seamJetH7 J,
    seamJetZ7 J,
    seamJetR7 J,
    seamJetP7 J,
    seamJetH8 J,
    seamJetZ8 J,
    seamJetR8 J,
    seamJetP8 J,
    seamJetH9 J,
    seamJetZ9 J,
    seamJetR9 J,
    seamJetP9 J,
    seamJetH10 J,
    seamJetZ10 J,
    seamJetR10 J,
    seamJetP10 J,
    seamJetH11 J,
    seamJetZ11 J,
    seamJetR11 J,
    seamJetP11 J,
    seamJetH12 J,
    seamJetZ12 J,
    seamJetR12 J,
    seamJetP12 J,
    seamJetH13 J,
    seamJetZ13 J,
    seamJetR13 J,
    seamJetP13 J] at e
  rw [e]
  try ring

/-- All four components at order 14. -/
theorem seamJetOrder14 {M R : ℂ} {h z r p : ℕ → ℂ} (J : SeamJetSystem M R h z r p) :
    h 14 = (-4784061619 / 128 : ℂ)*M^(1 : ℕ) + (144425158669 / 512 : ℂ)*M^(1 : ℕ)*R^(2 : ℕ) + (73336684785 / 2048 : ℂ)*M^(1 : ℕ)*R^(4 : ℕ) + (281360592513 / 8192 : ℂ)*M^(1 : ℕ)*R^(6 : ℕ) + (-91897207545 / 32768 : ℂ)*M^(1 : ℕ)*R^(8 : ℕ) + (-18226513305 / 131072 : ℂ)*M^(1 : ℕ)*R^(10 : ℕ) + (-2076072453 / 524288 : ℂ)*M^(1 : ℕ)*R^(12 : ℕ) + (82018251 / 2097152 : ℂ)*M^(1 : ℕ)*R^(14 : ℕ) ∧ z 14 = 0 ∧
      r 14 = (-1903757312 : ℂ)*R^(1 : ℕ) + (8585742848 : ℂ)*R^(3 : ℕ) + (-4329386880 : ℂ)*R^(5 : ℕ) + (636251616 : ℂ)*R^(7 : ℕ) + (-110218680 : ℂ)*R^(9 : ℕ) + (7261254 : ℂ)*R^(11 : ℕ) + (-176085 / 2 : ℂ)*R^(13 : ℕ) + (14301 / 8 : ℂ)*R^(15 : ℕ) ∧ p 14 = 0 :=
  ⟨seamJetH14 J, seamJetZ14 J, seamJetR14 J, seamJetP14 J⟩

end
end HTGeometry
