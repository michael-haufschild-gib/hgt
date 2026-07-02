/-
# Slice viability instances along `arg b` at modulus ≈ 3 — GENERATED FILE

Machine-generated square-tree escape certificates (generator:
`computations/rho_curve_recon/gen_slice.py`); every proof is rational arithmetic through the
coordinate-form disk-escape kit (`U0DiskEscape`).  Do not edit by hand — regenerate.
-/
import GaloisForLFunctions.U0.U0DiskEscape

open Complex Set Bottcher

namespace U0DichotomySlice

set_option maxHeartbeats 4000000


/-- Viable slice point: arg b ≈ 105.02°, ‖b‖ ≈ 3.0025 — the closed unit disk escapes. -/
theorem slice_viable_105 : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
  have nd3 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (161/40)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (20497/5000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd4 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1389/5000)) (c'i := (131/40)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32867/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd5 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-6389/5000)) (c'i := (131/40)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17577/5000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd6 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (121/40)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31233/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd2 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd3 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd4 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd5 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd6 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd8 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1389/5000)) (c'i := (101/40)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-35381/5000)) (c'i := (14971/10000)) (r' := (7911/2000)) (E := (1/10000)) (N := (25403/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9041/1250)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd10 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1007/2500)) (c'i := (9031/5000)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-38779/10000)) (c'i := (14449/10000)) (r' := (8487/5000)) (E := (1/10000)) (N := (9253/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (41383/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd11 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd12 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (5297/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-46621/10000)) (c'i := (-99/250)) (r' := (4189/2500)) (E := (1/10000)) (N := (22571/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11697/2500)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd14 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9653/10000)) (c'i := (4457/2500)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-30243/10000)) (c'i := (-5419/10000)) (r' := (8359/10000)) (E := (1/10000)) (N := (10137/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (323/40)) (c'i := (61777/10000)) (r' := (58413/10000)) (E := (1/10000)) (N := (1229/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10167/1000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd15 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (5/8)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd16 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2243/2000)) (c'i := (19859/10000)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17319/5000)) (c'i := (-1943/1250)) (r' := (2173/2500)) (E := (1/10000)) (N := (22807/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7593/2000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd17 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (1/2)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd13 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd14 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd15 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd16 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd17 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd9 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd10 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd11 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd12 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd13 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd18 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (111/40)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (28819/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd20 : ∀ z : ℂ, |z.re - (-3/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5139/5000)) (c'i := (3039/1250)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5279/2000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd21 : ∀ z : ℂ, |z.re - (-3/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3507/2500)) (c'i := (11219/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-19223/5000)) (c'i := (-2122/625)) (r' := (2089/1000)) (E := (1/10000)) (N := (26463/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (51291/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd22 : ∀ z : ℂ, |z.re - (-1/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1441/1250)) (c'i := (13719/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29761/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd23 : ∀ z : ℂ, |z.re - (-1/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-7639/5000)) (c'i := (6703/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30859/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd19 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd20 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd21 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd22 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd23 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd7 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd8 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd9 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd18 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd19 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd26 : ∀ z : ℂ, |z.re - (1/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-7639/5000)) (c'i := (6703/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30859/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd27 : ∀ z : ℂ, |z.re - (1/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1441/1250)) (c'i := (13719/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29761/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd28 : ∀ z : ℂ, |z.re - (3/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3507/2500)) (c'i := (11219/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-19223/5000)) (c'i := (-2122/625)) (r' := (2089/1000)) (E := (1/10000)) (N := (26463/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (51291/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd29 : ∀ z : ℂ, |z.re - (3/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5139/5000)) (c'i := (3039/1250)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5279/2000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd25 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd26 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd27 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd28 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd29 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd30 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (111/40)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (28819/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd33 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (1/2)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd34 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2243/2000)) (c'i := (19859/10000)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17319/5000)) (c'i := (-1943/1250)) (r' := (2173/2500)) (E := (1/10000)) (N := (22807/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7593/2000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd35 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (5/8)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd36 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9653/10000)) (c'i := (4457/2500)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-30243/10000)) (c'i := (-5419/10000)) (r' := (8359/10000)) (E := (1/10000)) (N := (10137/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (323/40)) (c'i := (61777/10000)) (r' := (58413/10000)) (E := (1/10000)) (N := (1229/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10167/1000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd32 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd33 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd34 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd35 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd36 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd37 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (5297/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-46621/10000)) (c'i := (-99/250)) (r' := (4189/2500)) (E := (1/10000)) (N := (22571/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11697/2500)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd38 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd39 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1007/2500)) (c'i := (9031/5000)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-38779/10000)) (c'i := (14449/10000)) (r' := (8487/5000)) (E := (1/10000)) (N := (9253/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (41383/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd31 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd32 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd37 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd38 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd39 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd40 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1389/5000)) (c'i := (101/40)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-35381/5000)) (c'i := (14971/10000)) (r' := (7911/2000)) (E := (1/10000)) (N := (25403/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9041/1250)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd24 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd25 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd30 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd31 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd40 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd42 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (121/40)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31233/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd43 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-6389/5000)) (c'i := (131/40)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17577/5000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd44 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1389/5000)) (c'i := (131/40)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32867/10000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd45 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3889/5000)) (c'i := (161/40)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (20497/5000)) (Nb := (1201/400)) (S := (3607/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd41 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd42 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd43 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd44 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd45 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd1 : ∀ z : ℂ, |z.re - (0)| ≤ (1) → |z.im - (0)| ≤ (1) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-7/9), (29/10)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd2 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd7 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd24 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd41 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  exact U0DiskEscape.viable_of_root_square nd1

/-- Viable slice point: arg b ≈ 125.05°, ‖b‖ ≈ 2.9860 — the closed unit disk escapes. -/
theorem slice_viable_125 : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
  have nd3 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (17847/5000)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39597/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd4 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-12143/10000)) (c'i := (14097/5000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30697/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd5 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22143/10000)) (c'i := (14097/5000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (35849/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd6 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (12847/5000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30887/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd2 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd3 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd4 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd5 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd6 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd9 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9643/10000)) (c'i := (22257/10000)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28691/5000)) (c'i := (-231/125)) (r' := (17919/10000)) (E := (1/10000)) (N := (24257/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15071/2500)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd10 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10893/10000)) (c'i := (8941/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18627/5000)) (c'i := (-14513/10000)) (r' := (16813/10000)) (E := (1/10000)) (N := (20939/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39981/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd11 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13393/10000)) (c'i := (11441/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26513/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd12 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-14643/10000)) (c'i := (19757/10000)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6947/2000)) (c'i := (-4177/1250)) (r' := (15099/10000)) (E := (1/10000)) (N := (1537/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (48199/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd8 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd9 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd10 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd11 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd12 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd15 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd16 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd17 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2741/2000)) (c'i := (1913/1250)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21781/10000)) (c'i := (-1094/625)) (r' := (7863/10000)) (E := (1/10000)) (N := (1284/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-341/10000)) (c'i := (20139/2000)) (r' := (50177/10000)) (E := (1/10000)) (N := (27943/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (20139/2000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd18 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3817/2500)) (c'i := (13273/10000)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-11449/10000)) (c'i := (-8043/5000)) (r' := (4171/5000)) (E := (1/10000)) (N := (20231/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-29911/10000)) (c'i := (30639/5000)) (r' := (39943/10000)) (E := (1/10000)) (N := (3949/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17047/2500)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd14 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd15 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd16 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd17 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd18 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd19 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd21 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-779/500)) (c'i := (1671/1000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2599/1250)) (c'i := (-3453/1250)) (r' := (1959/2500)) (E := (1/10000)) (N := (22847/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17287/5000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd22 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (14991/10000)) (r' := (1801/10000)) (E := (1/10000)) (N := (9723/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2557/2500)) (c'i := (-13477/5000)) (r' := (4269/5000)) (E := (1/10000)) (N := (11387/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-79333/10000)) (c'i := (39791/5000)) (r' := (28289/5000)) (E := (1/10000)) (N := (2883/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (112369/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd23 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (4529/2500)) (r' := (93/625)) (E := (1/10000)) (N := (1591/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24941/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd24 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3741/2000)) (c'i := (1671/1000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25081/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd20 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd21 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd22 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd23 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd24 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd26 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9509/5000)) (c'i := (13273/10000)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (88/625)) (c'i := (-26041/10000)) (r' := (9507/10000)) (E := (1/10000)) (N := (2899/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-42379/5000)) (c'i := (17111/10000)) (r' := (58687/10000)) (E := (1/10000)) (N := (326/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (86467/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd27 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (5/8)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd28 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1029/500)) (c'i := (1913/1250)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12823/5000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd29 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (1/2)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd25 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd26 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd27 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd28 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd29 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd13 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd14 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd19 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd20 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd25 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd30 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (11597/5000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (28841/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd31 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22143/10000)) (c'i := (10347/5000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30307/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd7 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd8 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd13 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd30 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd31 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd33 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22143/10000)) (c'i := (10347/5000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30307/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd34 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (11597/5000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (28841/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd37 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (1/2)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd38 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1029/500)) (c'i := (1913/1250)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12823/5000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd39 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-15/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (5/8)) (dy := (7/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd40 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-13/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9509/5000)) (c'i := (13273/10000)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (88/625)) (c'i := (-26041/10000)) (r' := (9507/10000)) (E := (1/10000)) (N := (2899/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-42379/5000)) (c'i := (17111/10000)) (r' := (58687/10000)) (E := (1/10000)) (N := (326/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (86467/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd36 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd37 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd38 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd39 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd40 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd42 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3741/2000)) (c'i := (1671/1000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25081/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd43 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (4529/2500)) (r' := (93/625)) (E := (1/10000)) (N := (1591/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24941/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd44 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (14991/10000)) (r' := (1801/10000)) (E := (1/10000)) (N := (9723/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2557/2500)) (c'i := (-13477/5000)) (r' := (4269/5000)) (E := (1/10000)) (N := (11387/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-79333/10000)) (c'i := (39791/5000)) (r' := (28289/5000)) (E := (1/10000)) (N := (2883/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (112369/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd45 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-779/500)) (c'i := (1671/1000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2599/1250)) (c'i := (-3453/1250)) (r' := (1959/2500)) (E := (1/10000)) (N := (22847/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17287/5000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd41 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd42 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd43 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd44 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd45 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd46 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd48 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3817/2500)) (c'i := (13273/10000)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-11449/10000)) (c'i := (-8043/5000)) (r' := (4171/5000)) (E := (1/10000)) (N := (20231/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-29911/10000)) (c'i := (30639/5000)) (r' := (39943/10000)) (E := (1/10000)) (N := (3949/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17047/2500)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd49 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2741/2000)) (c'i := (1913/1250)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21781/10000)) (c'i := (-1094/625)) (r' := (7863/10000)) (E := (1/10000)) (N := (1284/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-341/10000)) (c'i := (20139/2000)) (r' := (50177/10000)) (E := (1/10000)) (N := (27943/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (20139/2000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd50 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd51 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd47 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd48 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd49 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd50 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd51 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd35 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd36 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd41 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd46 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd47 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd53 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-14643/10000)) (c'i := (19757/10000)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6947/2000)) (c'i := (-4177/1250)) (r' := (15099/10000)) (E := (1/10000)) (N := (1537/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (48199/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd54 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13393/10000)) (c'i := (11441/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26513/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd55 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10893/10000)) (c'i := (8941/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18627/5000)) (c'i := (-14513/10000)) (r' := (16813/10000)) (E := (1/10000)) (N := (20939/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39981/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd56 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9643/10000)) (c'i := (22257/10000)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28691/5000)) (c'i := (-231/125)) (r' := (17919/10000)) (E := (1/10000)) (N := (24257/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15071/2500)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd52 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd53 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd54 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd55 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd56 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd32 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd33 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd34 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd35 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd52 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd58 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (12847/5000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30887/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd59 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22143/10000)) (c'i := (14097/5000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (35849/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd60 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-12143/10000)) (c'i := (14097/5000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30697/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd61 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-17143/10000)) (c'i := (17847/5000)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39597/10000)) (Nb := (29857/10000)) (S := (35977/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd57 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd58 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd59 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd60 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd61 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd1 : ∀ z : ℂ, |z.re - (0)| ≤ (1) → |z.im - (0)| ≤ (1) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-12/7), (22/9)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd2 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd7 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd32 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd57 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  exact U0DiskEscape.viable_of_root_square nd1

/-- Viable slice point: arg b ≈ 140.03°, ‖b‖ ≈ 3.0017 — the closed unit disk escapes. -/
theorem slice_viable_140 : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
  have nd3 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (3817/1250)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9557/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd4 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9/5)) (c'i := (5759/2500)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21833/5000)) (c'i := (-15911/2500)) (r' := (11203/2500)) (E := (1/10000)) (N := (5847/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (77183/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd5 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-14/5)) (c'i := (5759/2500)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (18129/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd6 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (2567/1250)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30833/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd2 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd3 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd4 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd5 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd6 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd9 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-31/20)) (c'i := (8549/5000)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28209/10000)) (c'i := (-16859/5000)) (r' := (8553/5000)) (E := (1/10000)) (N := (11539/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (43961/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd11 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3797/2500)) (c'i := (6713/5000)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8979/5000)) (c'i := (-21497/10000)) (r' := (1941/2500)) (E := (1/10000)) (N := (1267/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-36963/10000)) (c'i := (48247/5000)) (r' := (24787/5000)) (E := (1/10000)) (N := (28011/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (103331/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd12 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-129/80)) (c'i := (11083/10000)) (r' := (239/1250)) (E := (1/10000)) (N := (5173/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4641/5000)) (c'i := (-16457/10000)) (r' := (7857/10000)) (E := (1/10000)) (N := (19567/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10367/2500)) (c'i := (12459/2500)) (r' := (17951/5000)) (E := (1/10000)) (N := (3779/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4052/625)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd13 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-139/80)) (c'i := (888/625)) (r' := (1621/10000)) (E := (1/10000)) (N := (4353/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6499/5000)) (c'i := (-30087/10000)) (r' := (1887/2500)) (E := (1/10000)) (N := (4489/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16387/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd14 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2289/1250)) (c'i := (761/625)) (r' := (857/5000)) (E := (1/10000)) (N := (9229/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4293/10000)) (c'i := (-6327/2500)) (r' := (3921/5000)) (E := (1/10000)) (N := (21991/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-85207/10000)) (c'i := (8203/2000)) (r' := (23229/5000)) (E := (1/10000)) (N := (2567/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23641/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd10 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd11 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd12 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd13 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd14 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd15 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-77/40)) (c'i := (17723/10000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13083/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd16 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-41/20)) (c'i := (7299/5000)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-457/2000)) (c'i := (-20283/5000)) (r' := (1929/1250)) (E := (1/10000)) (N := (25167/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4063/1000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd8 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd9 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd10 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd15 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd16 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd19 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd20 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd22 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-18703/10000)) (c'i := (10321/10000)) (r' := (113/1250)) (E := (1/10000)) (N := (9971/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (83/625)) (c'i := (-19321/10000)) (r' := (3949/10000)) (E := (1/10000)) (N := (10681/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-30077/5000)) (c'i := (7077/5000)) (r' := (8437/5000)) (E := (1/10000)) (N := (19367/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15449/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd23 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9703/5000)) (c'i := (4633/5000)) (r' := (467/5000)) (E := (1/10000)) (N := (5159/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6073/10000)) (c'i := (-16677/10000)) (r' := (411/1000)) (E := (1/10000)) (N := (4301/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-11781/2500)) (c'i := (-97/1000)) (r' := (16297/10000)) (E := (1/10000)) (N := (17749/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (47133/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd24 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-19719/10000)) (c'i := (2197/2000)) (r' := (857/10000)) (E := (1/10000)) (N := (1181/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3817/10000)) (c'i := (-24037/10000)) (r' := (987/2500)) (E := (1/10000)) (N := (22573/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-79321/10000)) (c'i := (117/1250)) (r' := (20799/10000)) (E := (1/10000)) (N := (24339/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39663/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd25 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10211/5000)) (c'i := (1251/1250)) (r' := (89/1000)) (E := (1/10000)) (N := (9813/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (869/1000)) (c'i := (-21591/10000)) (r' := (4133/10000)) (E := (1/10000)) (N := (22743/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-31033/5000)) (c'i := (-18239/10000)) (r' := (2097/1000)) (E := (1/10000)) (N := (931/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6469/1000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd21 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd22 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd23 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd24 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd25 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd27 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd28 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd29 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21203/10000)) (c'i := (1129/1250)) (r' := (231/2500)) (E := (1/10000)) (N := (2551/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13799/10000)) (c'i := (-3803/2000)) (r' := (87/200)) (E := (1/10000)) (N := (23047/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10029/2500)) (c'i := (-4149/1250)) (r' := (22357/10000)) (E := (1/10000)) (N := (4699/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (52067/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd30 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd26 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd27 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd28 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd29 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd30 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd18 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd19 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd20 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd21 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd26 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd31 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd33 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10719/5000)) (c'i := (11551/10000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (601/625)) (c'i := (-378/125)) (r' := (4167/5000)) (E := (1/10000)) (N := (1522/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7933/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd34 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (9833/10000)) (r' := (1801/10000)) (E := (1/10000)) (N := (9723/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25013/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd35 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (6479/5000)) (r' := (93/625)) (E := (1/10000)) (N := (1591/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26399/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd36 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-12281/5000)) (c'i := (11551/10000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13571/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd32 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd33 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd34 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd35 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd36 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd37 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-107/40)) (c'i := (2087/2500)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14011/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd17 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd18 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd31 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd32 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd37 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd38 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (4509/2500)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7307/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd39 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-14/5)) (c'i := (971/625)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32021/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd7 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd8 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd17 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd38 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd39 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd41 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-14/5)) (c'i := (971/625)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32021/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd42 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (4509/2500)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7307/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd44 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-107/40)) (c'i := (2087/2500)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14011/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd46 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-12281/5000)) (c'i := (11551/10000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13571/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd47 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (6479/5000)) (r' := (93/625)) (E := (1/10000)) (N := (1591/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26399/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd48 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (9833/10000)) (r' := (1801/10000)) (E := (1/10000)) (N := (9723/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25013/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd49 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10719/5000)) (c'i := (11551/10000)) (r' := (1653/10000)) (E := (1/10000)) (N := (8883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (601/625)) (c'i := (-378/125)) (r' := (4167/5000)) (E := (1/10000)) (N := (1522/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7933/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd45 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd46 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd47 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd48 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd49 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd50 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd53 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd54 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21203/10000)) (c'i := (1129/1250)) (r' := (231/2500)) (E := (1/10000)) (N := (2551/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13799/10000)) (c'i := (-3803/2000)) (r' := (87/200)) (E := (1/10000)) (N := (23047/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10029/2500)) (c'i := (-4149/1250)) (r' := (22357/10000)) (E := (1/10000)) (N := (4699/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (52067/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd55 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd56 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd52 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd53 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd54 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd55 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd56 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd58 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10211/5000)) (c'i := (1251/1250)) (r' := (89/1000)) (E := (1/10000)) (N := (9813/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (869/1000)) (c'i := (-21591/10000)) (r' := (4133/10000)) (E := (1/10000)) (N := (22743/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-31033/5000)) (c'i := (-18239/10000)) (r' := (2097/1000)) (E := (1/10000)) (N := (931/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6469/1000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd59 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-19719/10000)) (c'i := (2197/2000)) (r' := (857/10000)) (E := (1/10000)) (N := (1181/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3817/10000)) (c'i := (-24037/10000)) (r' := (987/2500)) (E := (1/10000)) (N := (22573/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-79321/10000)) (c'i := (117/1250)) (r' := (20799/10000)) (E := (1/10000)) (N := (24339/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39663/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd60 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9703/5000)) (c'i := (4633/5000)) (r' := (467/5000)) (E := (1/10000)) (N := (5159/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6073/10000)) (c'i := (-16677/10000)) (r' := (411/1000)) (E := (1/10000)) (N := (4301/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-11781/2500)) (c'i := (-97/1000)) (r' := (16297/10000)) (E := (1/10000)) (N := (17749/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (47133/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd61 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-18703/10000)) (c'i := (10321/10000)) (r' := (113/1250)) (E := (1/10000)) (N := (9971/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (83/625)) (c'i := (-19321/10000)) (r' := (3949/10000)) (E := (1/10000)) (N := (10681/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-30077/5000)) (c'i := (7077/5000)) (r' := (8437/5000)) (E := (1/10000)) (N := (19367/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15449/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd57 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd58 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd59 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd60 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd61 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd62 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd63 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd51 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd52 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd57 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd62 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd63 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd43 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd44 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd45 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd50 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd51 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd65 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-41/20)) (c'i := (7299/5000)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-457/2000)) (c'i := (-20283/5000)) (r' := (1929/1250)) (E := (1/10000)) (N := (25167/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4063/1000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd66 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-77/40)) (c'i := (17723/10000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13083/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd68 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2289/1250)) (c'i := (761/625)) (r' := (857/5000)) (E := (1/10000)) (N := (9229/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4293/10000)) (c'i := (-6327/2500)) (r' := (3921/5000)) (E := (1/10000)) (N := (21991/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-85207/10000)) (c'i := (8203/2000)) (r' := (23229/5000)) (E := (1/10000)) (N := (2567/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23641/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd69 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-139/80)) (c'i := (888/625)) (r' := (1621/10000)) (E := (1/10000)) (N := (4353/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6499/5000)) (c'i := (-30087/10000)) (r' := (1887/2500)) (E := (1/10000)) (N := (4489/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16387/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd70 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-129/80)) (c'i := (11083/10000)) (r' := (239/1250)) (E := (1/10000)) (N := (5173/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4641/5000)) (c'i := (-16457/10000)) (r' := (7857/10000)) (E := (1/10000)) (N := (19567/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10367/2500)) (c'i := (12459/2500)) (r' := (17951/5000)) (E := (1/10000)) (N := (3779/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4052/625)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd71 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-3797/2500)) (c'i := (6713/5000)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8979/5000)) (c'i := (-21497/10000)) (r' := (1941/2500)) (E := (1/10000)) (N := (1267/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-36963/10000)) (c'i := (48247/5000)) (r' := (24787/5000)) (E := (1/10000)) (N := (28011/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (103331/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd67 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd68 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd69 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd70 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd71 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd72 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-31/20)) (c'i := (8549/5000)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28209/10000)) (c'i := (-16859/5000)) (r' := (8553/5000)) (E := (1/10000)) (N := (11539/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (43961/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd64 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd65 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd66 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd67 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd72 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd40 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd41 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd42 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd43 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd64 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd74 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (2567/1250)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30833/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd75 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-14/5)) (c'i := (5759/2500)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (18129/5000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd76 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9/5)) (c'i := (5759/2500)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21833/5000)) (c'i := (-15911/2500)) (r' := (11203/2500)) (E := (1/10000)) (N := (5847/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (77183/10000)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd77 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23/10)) (c'i := (3817/1250)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9557/2500)) (Nb := (1876/625)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd73 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd74 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd75 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd76 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd77 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd1 : ∀ z : ℂ, |z.re - (0)| ≤ (1) → |z.im - (0)| ≤ (1) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-23/10), (27/14)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd2 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd7 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd40 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd73 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  exact U0DiskEscape.viable_of_root_square nd1

/-- Viable slice point: arg b ≈ 150.02°, ‖b‖ ≈ 3.0017 — the closed unit disk escapes. -/
theorem slice_viable_150 : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
  have nd3 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (21/8)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (18473/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd5 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-79/40)) (c'i := (10781/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (731/250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd6 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-37/20)) (c'i := (4297/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10659/5000)) (c'i := (-12149/2500)) (r' := (9303/5000)) (E := (1/10000)) (N := (25253/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26533/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd7 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-47/20)) (c'i := (2461/1250)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30657/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd8 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-89/40)) (c'i := (8281/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (27737/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd4 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd5 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd6 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd7 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd8 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd9 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-31/10)) (c'i := (15/8)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (36229/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd10 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (13/8)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1533/500)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd2 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd3 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd4 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd9 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd10 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd14 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-69/40)) (c'i := (3457/2500)) (r' := (1743/10000)) (E := (1/10000)) (N := (2349/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3073/2000)) (c'i := (-32707/10000)) (r' := (8021/10000)) (E := (1/10000)) (N := (22109/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4517/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd15 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-8781/5000)) (c'i := (2871/2500)) (r' := (1773/10000)) (E := (1/10000)) (N := (9561/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4173/5000)) (c'i := (-3167/1250)) (r' := (1553/2000)) (E := (1/10000)) (N := (2623/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-41613/5000)) (c'i := (57291/10000)) (r' := (23753/5000)) (E := (1/10000)) (N := (6669/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (50519/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd16 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9719/5000)) (c'i := (874/625)) (r' := (1523/10000)) (E := (1/10000)) (N := (163/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1943/2500)) (c'i := (-9841/2500)) (r' := (1507/2000)) (E := (1/10000)) (N := (11973/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (40123/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd17 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-79/40)) (c'i := (11953/10000)) (r' := (389/2500)) (E := (1/10000)) (N := (8339/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1281/10000)) (c'i := (-16107/5000)) (r' := (1487/2000)) (E := (1/10000)) (N := (11543/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32239/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd13 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd14 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd15 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd16 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd17 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd19 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4547/2500)) (c'i := (9141/10000)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-51/400)) (c'i := (-18251/10000)) (r' := (3897/5000)) (E := (1/10000)) (N := (5089/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-59147/10000)) (c'i := (9827/5000)) (r' := (34631/10000)) (E := (1/10000)) (N := (2287/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31163/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd21 : ∀ z : ℂ, |z.re - (-31/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (3/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd22 : ∀ z : ℂ, |z.re - (-31/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd23 : ∀ z : ℂ, |z.re - (-29/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9719/5000)) (c'i := (7637/10000)) (r' := (9/100)) (E := (1/10000)) (N := (2483/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5951/10000)) (c'i := (-1469/1000)) (r' := (1923/5000)) (E := (1/10000)) (N := (4177/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-22019/5000)) (c'i := (-621/2500)) (r' := (6843/5000)) (E := (1/10000)) (N := (317/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (44107/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd25 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd26 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (15/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd27 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20121/10000)) (c'i := (6929/10000)) (r' := (449/10000)) (E := (1/10000)) (N := (9993/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2421/2500)) (c'i := (-3221/2500)) (r' := (387/2000)) (E := (1/10000)) (N := (21281/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16611/5000)) (c'i := (-4977/5000)) (r' := (331/500)) (E := (1/10000)) (N := (8059/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (34681/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd28 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10207/5000)) (c'i := (1593/2500)) (r' := (91/2000)) (E := (1/10000)) (N := (10139/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11613/10000)) (c'i := (-1377/1250)) (r' := (197/1000)) (E := (1/10000)) (N := (10693/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-24649/10000)) (c'i := (-5293/5000)) (r' := (6703/10000)) (E := (1/10000)) (N := (16007/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (23551/10000)) (c'i := (67187/10000)) (r' := (40499/10000)) (E := (1/10000)) (N := (26827/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14239/2000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd24 : ∀ z : ℂ, |z.re - (-29/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd25 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd26 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd27 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd28 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd20 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd21 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd22 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd23 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd24 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd29 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-163/80)) (c'i := (4961/5000)) (r' := (1621/10000)) (E := (1/10000)) (N := (4353/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5669/10000)) (c'i := (-3179/1250)) (r' := (7619/10000)) (E := (1/10000)) (N := (22663/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17493/2000)) (c'i := (-2767/2000)) (r' := (22779/5000)) (E := (1/10000)) (N := (26057/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11069/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd31 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20531/10000)) (c'i := (1629/2000)) (r' := (17/200)) (E := (1/10000)) (N := (1873/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4759/5000)) (c'i := (-3689/2000)) (r' := (3833/10000)) (E := (1/10000)) (N := (2761/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-50963/10000)) (c'i := (-1257/625)) (r' := (87/50)) (E := (1/10000)) (N := (5189/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (54787/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd33 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5167/2500)) (c'i := (1803/2500)) (r' := (109/2500)) (E := (1/10000)) (N := (2429/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2303/2000)) (c'i := (-3703/2500)) (r' := (1931/10000)) (E := (1/10000)) (N := (21891/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-867/250)) (c'i := (-2389/1250)) (r' := (1907/2500)) (E := (1/10000)) (N := (9381/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39597/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd34 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20961/10000)) (c'i := (267/400)) (r' := (443/10000)) (E := (1/10000)) (N := (1973/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13481/10000)) (c'i := (-12983/10000)) (r' := (493/2500)) (E := (1/10000)) (N := (21999/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12341/5000)) (c'i := (-4001/2000)) (r' := (389/500)) (E := (1/10000)) (N := (18717/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31771/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd35 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4239/2000)) (c'i := (1499/2000)) (r' := (53/1250)) (E := (1/10000)) (N := (118/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2661/2000)) (c'i := (-16771/10000)) (r' := (241/1250)) (E := (1/10000)) (N := (11241/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4553/1250)) (c'i := (-7407/2500)) (r' := (8637/10000)) (E := (1/10000)) (N := (1338/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5869/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd36 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1343/625)) (c'i := (3489/5000)) (r' := (431/10000)) (E := (1/10000)) (N := (4797/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1913/1250)) (c'i := (-14989/10000)) (r' := (197/1000)) (E := (1/10000)) (N := (22593/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12523/5000)) (c'i := (-15439/5000)) (r' := (8839/10000)) (E := (1/10000)) (N := (10711/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (19879/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd32 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd33 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd34 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd35 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd36 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd37 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21547/10000)) (c'i := (2163/2500)) (r' := (801/10000)) (E := (1/10000)) (N := (4403/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6471/5000)) (c'i := (-4457/2000)) (r' := (3789/10000)) (E := (1/10000)) (N := (1161/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-58913/10000)) (c'i := (-21341/5000)) (r' := (20987/10000)) (E := (1/10000)) (N := (25771/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (72749/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd38 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11047/5000)) (c'i := (1919/2500)) (r' := (207/2500)) (E := (1/10000)) (N := (9111/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8461/5000)) (c'i := (-18919/10000)) (r' := (3947/10000)) (E := (1/10000)) (N := (2339/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-33157/10000)) (c'i := (-49029/10000)) (r' := (10809/5000)) (E := (1/10000)) (N := (25383/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14797/2500)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd30 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd31 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd32 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd37 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd38 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd18 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd19 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd20 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd29 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd30 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd39 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-89/40)) (c'i := (6719/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25993/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd41 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-89/40)) (c'i := (10703/10000)) (r' := (1417/10000)) (E := (1/10000)) (N := (472/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2469/1000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd42 : ∀ z : ℂ, |z.re - (-11/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5797/2500)) (c'i := (1123/1250)) (r' := (1523/10000)) (E := (1/10000)) (N := (163/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24867/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd43 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5953/2500)) (c'i := (2871/2500)) (r' := (1219/10000)) (E := (1/10000)) (N := (1287/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6609/2500)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd44 : ∀ z : ℂ, |z.re - (-9/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-99/40)) (c'i := (5039/5000)) (r' := (671/5000)) (E := (1/10000)) (N := (7127/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26723/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd40 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd41 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd42 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd43 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd44 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd12 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd13 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd18 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd39 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd40 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd47 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd48 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd51 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21273/10000)) (c'i := (3069/5000)) (r' := (9/200)) (E := (1/10000)) (N := (5011/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15487/10000)) (c'i := (-2223/2000)) (r' := (126/625)) (E := (1/10000)) (N := (22141/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1437/1000)) (c'i := (-4857/2500)) (r' := (4051/5000)) (E := (1/10000)) (N := (19063/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8619/2000)) (c'i := (17709/2500)) (r' := (5721/1250)) (E := (1/10000)) (N := (4833/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16583/2000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd53 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (17/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd54 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd55 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10827/5000)) (c'i := (5819/10000)) (r' := (113/5000)) (E := (1/10000)) (N := (10079/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17503/10000)) (c'i := (-10201/10000)) (r' := (1021/10000)) (E := (1/10000)) (N := (22423/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5771/10000)) (c'i := (-2071/1000)) (r' := (4247/10000)) (E := (1/10000)) (N := (20259/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1639/250)) (c'i := (38903/10000)) (r' := (20087/10000)) (E := (1/10000)) (N := (43/20)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (76233/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd56 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd52 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd53 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd54 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd55 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd56 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd57 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21801/10000)) (c'i := (323/500)) (r' := (219/5000)) (E := (1/10000)) (N := (2439/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3471/2000)) (c'i := (-13167/10000)) (r' := (403/2000)) (E := (1/10000)) (N := (11369/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-13217/10000)) (c'i := (-30703/10000)) (r' := (2299/2500)) (E := (1/10000)) (N := (4357/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16713/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd58 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22133/10000)) (c'i := (2971/5000)) (r' := (223/5000)) (E := (1/10000)) (N := (397/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1216/625)) (c'i := (-11303/10000)) (r' := (517/2500)) (E := (1/10000)) (N := (22917/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-461/5000)) (c'i := (-14491/5000)) (r' := (1949/2000)) (E := (1/10000)) (N := (22501/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-109911/10000)) (c'i := (2543/1250)) (r' := (66079/10000)) (E := (1/10000)) (N := (28997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (111777/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd50 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd51 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd52 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd57 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd58 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd60 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (37/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (9/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd61 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (39/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (19/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd63 : ∀ z : ℂ, |z.re - (-107/128)| ≤ (1/128) → |z.im - (73/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (53/64)) (dy := (9/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd64 : ∀ z : ℂ, |z.re - (-107/128)| ≤ (1/128) → |z.im - (75/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (53/64)) (dy := (37/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd65 : ∀ z : ℂ, |z.re - (-105/128)| ≤ (1/128) → |z.im - (73/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22523/10000)) (c'i := (5643/10000)) (r' := (14/625)) (E := (1/10000)) (N := (9991/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2693/1250)) (c'i := (-10419/10000)) (r' := (131/1250)) (E := (1/10000)) (N := (1161/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9559/10000)) (c'i := (-29893/10000)) (r' := (5133/10000)) (E := (1/10000)) (N := (5983/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (3923/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd66 : ∀ z : ℂ, |z.re - (-105/128)| ≤ (1/128) → |z.im - (75/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1419/625)) (c'i := (5387/10000)) (r' := (113/5000)) (E := (1/10000)) (N := (10081/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11667/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd62 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (37/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd63 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd64 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd65 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd66 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd67 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (39/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (19/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd59 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd60 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd61 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd62 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd67 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd68 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22719/10000)) (c'i := (6699/10000)) (r' := (857/10000)) (E := (1/10000)) (N := (1181/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2641/1250)) (c'i := (-15439/10000)) (r' := (4139/10000)) (E := (1/10000)) (N := (23687/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5197/10000)) (c'i := (-50239/10000)) (r' := (117/50)) (E := (1/10000)) (N := (3271/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (50507/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd69 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11711/5000)) (c'i := (5723/10000)) (r' := (89/1000)) (E := (1/10000)) (N := (9813/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24111/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd49 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd50 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd59 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd68 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd69 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd71 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd72 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd73 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-24203/10000)) (c'i := (2373/5000)) (r' := (231/2500)) (E := (1/10000)) (N := (2551/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24663/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd74 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd70 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd71 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd72 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd73 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd74 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd46 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd47 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd48 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd49 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd70 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd75 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd76 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (1797/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1079/400)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd77 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-119/40)) (c'i := (2031/5000)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1201/400)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd45 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd46 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd75 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd76 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd77 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd78 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (11/8)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29411/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd79 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-31/10)) (c'i := (9/8)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16489/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd11 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd12 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd45 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd78 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd79 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd81 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-31/10)) (c'i := (9/8)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16489/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd82 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (11/8)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29411/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd84 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-119/40)) (c'i := (2031/5000)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1201/400)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd85 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (1797/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1079/400)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd86 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd89 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd90 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-24203/10000)) (c'i := (2373/5000)) (r' := (231/2500)) (E := (1/10000)) (N := (2551/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24663/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd91 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-23/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (11/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd92 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-21/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd88 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd89 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd90 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd91 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd92 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd94 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11711/5000)) (c'i := (5723/10000)) (r' := (89/1000)) (E := (1/10000)) (N := (9813/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24111/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd95 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22719/10000)) (c'i := (6699/10000)) (r' := (857/10000)) (E := (1/10000)) (N := (1181/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2641/1250)) (c'i := (-15439/10000)) (r' := (4139/10000)) (E := (1/10000)) (N := (23687/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5197/10000)) (c'i := (-50239/10000)) (r' := (117/50)) (E := (1/10000)) (N := (3271/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (50507/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd97 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-39/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (13/16)) (dy := (19/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd99 : ∀ z : ℂ, |z.re - (105/128)| ≤ (1/128) → |z.im - (-75/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1419/625)) (c'i := (5387/10000)) (r' := (113/5000)) (E := (1/10000)) (N := (10081/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11667/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd100 : ∀ z : ℂ, |z.re - (105/128)| ≤ (1/128) → |z.im - (-73/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22523/10000)) (c'i := (5643/10000)) (r' := (14/625)) (E := (1/10000)) (N := (9991/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2693/1250)) (c'i := (-10419/10000)) (r' := (131/1250)) (E := (1/10000)) (N := (1161/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9559/10000)) (c'i := (-29893/10000)) (r' := (5133/10000)) (E := (1/10000)) (N := (5983/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (3923/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd101 : ∀ z : ℂ, |z.re - (107/128)| ≤ (1/128) → |z.im - (-75/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (53/64)) (dy := (37/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd102 : ∀ z : ℂ, |z.re - (107/128)| ≤ (1/128) → |z.im - (-73/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (53/64)) (dy := (9/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd98 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-37/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd99 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd100 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd101 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd102 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd103 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-39/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (19/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd104 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-37/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (9/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd96 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd97 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd98 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd103 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd104 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd106 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22133/10000)) (c'i := (2971/5000)) (r' := (223/5000)) (E := (1/10000)) (N := (397/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1216/625)) (c'i := (-11303/10000)) (r' := (517/2500)) (E := (1/10000)) (N := (22917/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-461/5000)) (c'i := (-14491/5000)) (r' := (1949/2000)) (E := (1/10000)) (N := (22501/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-109911/10000)) (c'i := (2543/1250)) (r' := (66079/10000)) (E := (1/10000)) (N := (28997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (111777/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd107 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21801/10000)) (c'i := (323/500)) (r' := (219/5000)) (E := (1/10000)) (N := (2439/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3471/2000)) (c'i := (-13167/10000)) (r' := (403/2000)) (E := (1/10000)) (N := (11369/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-13217/10000)) (c'i := (-30703/10000)) (r' := (2299/2500)) (E := (1/10000)) (N := (4357/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16713/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd109 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd110 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10827/5000)) (c'i := (5819/10000)) (r' := (113/5000)) (E := (1/10000)) (N := (10079/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17503/10000)) (c'i := (-10201/10000)) (r' := (1021/10000)) (E := (1/10000)) (N := (22423/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5771/10000)) (c'i := (-2071/1000)) (r' := (4247/10000)) (E := (1/10000)) (N := (20259/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1639/250)) (c'i := (38903/10000)) (r' := (20087/10000)) (E := (1/10000)) (N := (43/20)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (76233/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd111 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd112 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (17/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd108 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd109 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd110 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd111 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd112 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd113 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21273/10000)) (c'i := (3069/5000)) (r' := (9/200)) (E := (1/10000)) (N := (5011/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15487/10000)) (c'i := (-2223/2000)) (r' := (126/625)) (E := (1/10000)) (N := (22141/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1437/1000)) (c'i := (-4857/2500)) (r' := (4051/5000)) (E := (1/10000)) (N := (19063/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8619/2000)) (c'i := (17709/2500)) (r' := (5721/1250)) (E := (1/10000)) (N := (4833/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16583/2000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd105 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd106 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd107 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd108 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd113 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd93 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd94 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd95 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd96 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd105 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd114 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd115 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd87 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd88 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd93 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd114 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd115 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd83 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd84 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd85 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd86 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd87 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd118 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-99/40)) (c'i := (5039/5000)) (r' := (671/5000)) (E := (1/10000)) (N := (7127/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26723/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd119 : ∀ z : ℂ, |z.re - (9/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5953/2500)) (c'i := (2871/2500)) (r' := (1219/10000)) (E := (1/10000)) (N := (1287/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6609/2500)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd120 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5797/2500)) (c'i := (1123/1250)) (r' := (1523/10000)) (E := (1/10000)) (N := (163/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24867/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd121 : ∀ z : ℂ, |z.re - (11/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-89/40)) (c'i := (10703/10000)) (r' := (1417/10000)) (E := (1/10000)) (N := (472/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2469/1000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd117 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd118 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd119 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd120 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd121 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd122 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-89/40)) (c'i := (6719/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25993/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd125 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11047/5000)) (c'i := (1919/2500)) (r' := (207/2500)) (E := (1/10000)) (N := (9111/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8461/5000)) (c'i := (-18919/10000)) (r' := (3947/10000)) (E := (1/10000)) (N := (2339/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-33157/10000)) (c'i := (-49029/10000)) (r' := (10809/5000)) (E := (1/10000)) (N := (25383/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14797/2500)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd126 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21547/10000)) (c'i := (2163/2500)) (r' := (801/10000)) (E := (1/10000)) (N := (4403/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6471/5000)) (c'i := (-4457/2000)) (r' := (3789/10000)) (E := (1/10000)) (N := (1161/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-58913/10000)) (c'i := (-21341/5000)) (r' := (20987/10000)) (E := (1/10000)) (N := (25771/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (72749/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd128 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1343/625)) (c'i := (3489/5000)) (r' := (431/10000)) (E := (1/10000)) (N := (4797/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1913/1250)) (c'i := (-14989/10000)) (r' := (197/1000)) (E := (1/10000)) (N := (22593/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12523/5000)) (c'i := (-15439/5000)) (r' := (8839/10000)) (E := (1/10000)) (N := (10711/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (19879/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd129 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4239/2000)) (c'i := (1499/2000)) (r' := (53/1250)) (E := (1/10000)) (N := (118/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2661/2000)) (c'i := (-16771/10000)) (r' := (241/1250)) (E := (1/10000)) (N := (11241/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4553/1250)) (c'i := (-7407/2500)) (r' := (8637/10000)) (E := (1/10000)) (N := (1338/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5869/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd130 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20961/10000)) (c'i := (267/400)) (r' := (443/10000)) (E := (1/10000)) (N := (1973/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13481/10000)) (c'i := (-12983/10000)) (r' := (493/2500)) (E := (1/10000)) (N := (21999/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12341/5000)) (c'i := (-4001/2000)) (r' := (389/500)) (E := (1/10000)) (N := (18717/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31771/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd131 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5167/2500)) (c'i := (1803/2500)) (r' := (109/2500)) (E := (1/10000)) (N := (2429/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2303/2000)) (c'i := (-3703/2500)) (r' := (1931/10000)) (E := (1/10000)) (N := (21891/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-867/250)) (c'i := (-2389/1250)) (r' := (1907/2500)) (E := (1/10000)) (N := (9381/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39597/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd127 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd128 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd129 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd130 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd131 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd132 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20531/10000)) (c'i := (1629/2000)) (r' := (17/200)) (E := (1/10000)) (N := (1873/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4759/5000)) (c'i := (-3689/2000)) (r' := (3833/10000)) (E := (1/10000)) (N := (2761/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-50963/10000)) (c'i := (-1257/625)) (r' := (87/50)) (E := (1/10000)) (N := (5189/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (54787/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd124 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd125 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd126 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd127 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd132 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd133 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-163/80)) (c'i := (4961/5000)) (r' := (1621/10000)) (E := (1/10000)) (N := (4353/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5669/10000)) (c'i := (-3179/1250)) (r' := (7619/10000)) (E := (1/10000)) (N := (22663/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17493/2000)) (c'i := (-2767/2000)) (r' := (22779/5000)) (E := (1/10000)) (N := (26057/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11069/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd136 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10207/5000)) (c'i := (1593/2500)) (r' := (91/2000)) (E := (1/10000)) (N := (10139/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11613/10000)) (c'i := (-1377/1250)) (r' := (197/1000)) (E := (1/10000)) (N := (10693/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-24649/10000)) (c'i := (-5293/5000)) (r' := (6703/10000)) (E := (1/10000)) (N := (16007/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (23551/10000)) (c'i := (67187/10000)) (r' := (40499/10000)) (E := (1/10000)) (N := (26827/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14239/2000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd137 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20121/10000)) (c'i := (6929/10000)) (r' := (449/10000)) (E := (1/10000)) (N := (9993/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2421/2500)) (c'i := (-3221/2500)) (r' := (387/2000)) (E := (1/10000)) (N := (21281/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16611/5000)) (c'i := (-4977/5000)) (r' := (331/500)) (E := (1/10000)) (N := (8059/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (34681/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd138 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (15/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd139 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd135 : ∀ z : ℂ, |z.re - (29/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd136 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd137 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd138 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd139 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd140 : ∀ z : ℂ, |z.re - (29/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9719/5000)) (c'i := (7637/10000)) (r' := (9/100)) (E := (1/10000)) (N := (2483/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5951/10000)) (c'i := (-1469/1000)) (r' := (1923/5000)) (E := (1/10000)) (N := (4177/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-22019/5000)) (c'i := (-621/2500)) (r' := (6843/5000)) (E := (1/10000)) (N := (317/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (44107/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd141 : ∀ z : ℂ, |z.re - (31/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd142 : ∀ z : ℂ, |z.re - (31/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (3/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd134 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd135 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd140 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd141 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd142 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd143 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4547/2500)) (c'i := (9141/10000)) (r' := (183/1000)) (E := (1/10000)) (N := (9883/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-51/400)) (c'i := (-18251/10000)) (r' := (3897/5000)) (E := (1/10000)) (N := (5089/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-59147/10000)) (c'i := (9827/5000)) (r' := (34631/10000)) (E := (1/10000)) (N := (2287/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31163/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd123 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd124 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd133 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd134 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd143 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd145 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-79/40)) (c'i := (11953/10000)) (r' := (389/2500)) (E := (1/10000)) (N := (8339/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1281/10000)) (c'i := (-16107/5000)) (r' := (1487/2000)) (E := (1/10000)) (N := (11543/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32239/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd146 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9719/5000)) (c'i := (874/625)) (r' := (1523/10000)) (E := (1/10000)) (N := (163/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1943/2500)) (c'i := (-9841/2500)) (r' := (1507/2000)) (E := (1/10000)) (N := (11973/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (40123/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd147 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-8781/5000)) (c'i := (2871/2500)) (r' := (1773/10000)) (E := (1/10000)) (N := (9561/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4173/5000)) (c'i := (-3167/1250)) (r' := (1553/2000)) (E := (1/10000)) (N := (2623/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-41613/5000)) (c'i := (57291/10000)) (r' := (23753/5000)) (E := (1/10000)) (N := (6669/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (50519/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd148 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-69/40)) (c'i := (3457/2500)) (r' := (1743/10000)) (E := (1/10000)) (N := (2349/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3073/2000)) (c'i := (-32707/10000)) (r' := (8021/10000)) (E := (1/10000)) (N := (22109/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4517/1250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd144 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd145 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd146 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd147 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd148 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd116 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd117 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd122 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd123 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd144 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd80 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd81 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd82 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd83 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd116 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd150 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (13/8)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1533/500)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd151 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-31/10)) (c'i := (15/8)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (36229/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd153 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-89/40)) (c'i := (8281/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (27737/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd154 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-47/20)) (c'i := (2461/1250)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30657/10000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd155 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-37/20)) (c'i := (4297/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10659/5000)) (c'i := (-12149/2500)) (r' := (9303/5000)) (E := (1/10000)) (N := (25253/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (26533/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd156 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-79/40)) (c'i := (10781/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (731/250)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd152 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd153 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd154 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd155 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd156 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd157 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-13/5)) (c'i := (21/8)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (18473/5000)) (Nb := (30017/10000)) (S := (7213/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd149 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd150 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd151 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd152 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd157 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd1 : ∀ z : ℂ, |z.re - (0)| ≤ (1) → |z.im - (0)| ≤ (1) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-13/5), (3/2)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd2 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd11 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd80 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd149 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  exact U0DiskEscape.viable_of_root_square nd1

end U0DichotomySlice
