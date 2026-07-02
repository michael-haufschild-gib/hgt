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


/-- Viable slice point: arg b ≈ 155.43°, ‖b‖ ≈ 3.0017 — the closed unit disk escapes. -/
theorem slice_viable_155 : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
  have nd3 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (2373/1000)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (36171/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd5 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-421/200)) (c'i := (9521/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1774/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd6 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-99/50)) (c'i := (3667/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9611/10000)) (c'i := (-9121/2000)) (r' := (3637/2000)) (E := (1/10000)) (N := (12321/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23303/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd7 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-62/25)) (c'i := (1073/625)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15081/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd8 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-471/200)) (c'i := (7021/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13709/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd4 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd5 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd6 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd7 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd8 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd9 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-323/100)) (c'i := (1623/1000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9037/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd10 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (1373/1000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15279/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd2 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd3 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd4 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd9 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd10 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd14 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-371/200)) (c'i := (2827/2500)) (r' := (1743/10000)) (E := (1/10000)) (N := (2349/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5677/10000)) (c'i := (-29473/10000)) (r' := (7887/10000)) (E := (1/10000)) (N := (869/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-110943/10000)) (c'i := (5743/1250)) (r' := (53621/10000)) (E := (1/10000)) (N := (6003/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (120079/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd15 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9431/5000)) (c'i := (2241/2500)) (r' := (1773/10000)) (E := (1/10000)) (N := (9561/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (121/5000)) (c'i := (-2667/1250)) (r' := (7729/10000)) (E := (1/10000)) (N := (5221/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-72817/10000)) (c'i := (11447/10000)) (r' := (19499/5000)) (E := (1/10000)) (N := (10669/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (73711/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd16 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10369/5000)) (c'i := (1433/1250)) (r' := (1523/10000)) (E := (1/10000)) (N := (163/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (641/2500)) (c'i := (-8767/2500)) (r' := (7459/10000)) (E := (1/10000)) (N := (1481/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (35161/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd17 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-421/200)) (c'i := (9433/10000)) (r' := (389/2500)) (E := (1/10000)) (N := (8339/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (507/625)) (c'i := (-27233/10000)) (r' := (7429/10000)) (E := (1/10000)) (N := (23067/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-94883/10000)) (c'i := (-31703/10000)) (r' := (47789/10000)) (E := (1/10000)) (N := (1776/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (100039/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd13 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd14 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd15 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd16 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd17 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd20 : ∀ z : ℂ, |z.re - (-31/32)| ≤ (1/32) → |z.im - (9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9353/5000)) (c'i := (7031/10000)) (r' := (457/5000)) (E := (1/10000)) (N := (1261/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (687/2500)) (c'i := (-864/625)) (r' := (1871/5000)) (E := (1/10000)) (N := (1249/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9131/2000)) (c'i := (2441/5000)) (r' := (5981/5000)) (E := (1/10000)) (N := (2819/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9183/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd21 : ∀ z : ℂ, |z.re - (-31/32)| ≤ (1/32) → |z.im - (11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-19097/10000)) (c'i := (291/500)) (r' := (931/10000)) (E := (1/10000)) (N := (257/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2891/5000)) (c'i := (-9749/10000)) (r' := (3809/10000)) (E := (1/10000)) (N := (3993/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-33461/10000)) (c'i := (603/5000)) (r' := (10097/10000)) (E := (1/10000)) (N := (2267/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16741/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd22 : ∀ z : ℂ, |z.re - (-29/32)| ≤ (1/32) → |z.im - (9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9939/5000)) (c'i := (3691/5000)) (r' := (861/10000)) (E := (1/10000)) (N := (9489/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1691/2500)) (c'i := (-4217/2500)) (r' := (3731/10000)) (E := (1/10000)) (N := (4241/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-25589/5000)) (c'i := (-10339/10000)) (r' := (1497/1000)) (E := (1/10000)) (N := (9087/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (52211/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd24 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (21/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9939/5000)) (c'i := (643/1000)) (r' := (11/250)) (E := (1/10000)) (N := (4893/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8079/10000)) (c'i := (-13083/10000)) (r' := (1861/10000)) (E := (1/10000)) (N := (20893/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-37889/10000)) (c'i := (-433/500)) (r' := (6077/10000)) (E := (1/10000)) (N := (15377/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (19433/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd25 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (23/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20093/10000)) (c'i := (2927/5000)) (r' := (111/2500)) (E := (1/10000)) (N := (1979/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4823/5000)) (c'i := (-2209/2000)) (r' := (941/5000)) (E := (1/10000)) (N := (20929/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6039/2000)) (c'i := (-2207/2500)) (r' := (5881/10000)) (E := (1/10000)) (N := (2933/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31459/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd26 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (21/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4089/2000)) (c'i := (1327/2000)) (r' := (427/10000)) (E := (1/10000)) (N := (2373/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10097/10000)) (c'i := (-14651/10000)) (r' := (1857/10000)) (E := (1/10000)) (N := (4299/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3857/1000)) (c'i := (-8553/5000)) (r' := (3481/5000)) (E := (1/10000)) (N := (8897/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (42193/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd27 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (23/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20659/10000)) (c'i := (6079/10000)) (r' := (431/10000)) (E := (1/10000)) (N := (2401/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2921/2500)) (c'i := (-12637/10000)) (r' := (939/5000)) (E := (1/10000)) (N := (4307/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-14809/5000)) (c'i := (-341/200)) (r' := (273/400)) (E := (1/10000)) (N := (17211/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17087/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd23 : ∀ z : ℂ, |z.re - (-29/32)| ≤ (1/32) → |z.im - (11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd24 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd25 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd26 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd27 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd19 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd20 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd21 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd22 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd23 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd29 : ∀ z : ℂ, |z.re - (-31/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (3/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd30 : ∀ z : ℂ, |z.re - (-31/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd33 : ∀ z : ℂ, |z.re - (-119/128)| ≤ (1/128) → |z.im - (49/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10061/5000)) (c'i := (2681/5000)) (r' := (9/400)) (E := (1/10000)) (N := (2011/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5157/5000)) (c'i := (-9099/10000)) (r' := (189/2000)) (E := (1/10000)) (N := (833/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-24941/10000)) (c'i := (-6289/10000)) (r' := (2693/10000)) (E := (1/10000)) (N := (6877/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (619/200)) (c'i := (43851/10000)) (r' := (2919/2000)) (E := (1/10000)) (N := (12861/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (53673/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd34 : ∀ z : ℂ, |z.re - (-119/128)| ≤ (1/128) → |z.im - (51/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (59/64)) (dy := (25/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd35 : ∀ z : ℂ, |z.re - (-117/128)| ≤ (1/128) → |z.im - (49/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2041/1000)) (c'i := (2741/5000)) (r' := (111/5000)) (E := (1/10000)) (N := (991/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1419/1250)) (c'i := (-4949/5000)) (r' := (473/5000)) (E := (1/10000)) (N := (10567/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2421/1000)) (c'i := (-1249/1250)) (r' := (184/625)) (E := (1/10000)) (N := (7531/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2619/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd36 : ∀ z : ℂ, |z.re - (-117/128)| ≤ (1/128) → |z.im - (51/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5133/2500)) (c'i := (1299/2500)) (r' := (223/10000)) (E := (1/10000)) (N := (2493/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3039/2500)) (c'i := (-8857/10000)) (r' := (119/1250)) (E := (1/10000)) (N := (1059/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1273/625)) (c'i := (-9053/10000)) (r' := (2959/10000)) (E := (1/10000)) (N := (15041/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (599/1000)) (c'i := (24679/5000)) (r' := (7041/5000)) (E := (1/10000)) (N := (2229/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1243/250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd32 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd33 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd34 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd35 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd36 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd38 : ∀ z : ℂ, |z.re - (-119/128)| ≤ (1/128) → |z.im - (53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (59/64)) (dy := (13/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd39 : ∀ z : ℂ, |z.re - (-119/128)| ≤ (1/128) → |z.im - (55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (59/64)) (dy := (27/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd40 : ∀ z : ℂ, |z.re - (-117/128)| ≤ (1/128) → |z.im - (53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20659/10000)) (c'i := (491/1000)) (r' := (9/400)) (E := (1/10000)) (N := (2007/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12969/10000)) (c'i := (-7807/10000)) (r' := (963/10000)) (E := (1/10000)) (N := (4247/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-663/400)) (c'i := (-777/1000)) (r' := (3013/10000)) (E := (1/10000)) (N := (7569/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-733/1250)) (c'i := (19119/5000)) (r' := (747/625)) (E := (1/10000)) (N := (9153/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9671/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd41 : ∀ z : ℂ, |z.re - (-117/128)| ≤ (1/128) → |z.im - (55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20791/10000)) (c'i := (37/80)) (r' := (113/5000)) (E := (1/10000)) (N := (10101/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3447/2500)) (c'i := (-422/625)) (r' := (97/1000)) (E := (1/10000)) (N := (213/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-803/625)) (c'i := (-6139/10000)) (r' := (3077/10000)) (E := (1/10000)) (N := (15353/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7281/5000)) (c'i := (5651/2000)) (r' := (9721/10000)) (E := (1/10000)) (N := (178/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-85929/10000)) (c'i := (-6981/1000)) (r' := (71323/10000)) (E := (1/10000)) (N := (31787/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13839/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd37 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd38 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd39 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd40 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd41 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd42 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10447/5000)) (c'i := (2761/5000)) (r' := (437/10000)) (E := (1/10000)) (N := (4863/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13307/10000)) (c'i := (-2119/2000)) (r' := (1911/10000)) (E := (1/10000)) (N := (5403/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10409/5000)) (c'i := (-7859/5000)) (r' := (11/16)) (E := (1/10000)) (N := (1701/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8667/10000)) (c'i := (77923/10000)) (r' := (40637/10000)) (E := (1/10000)) (N := (13043/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (78403/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd44 : ∀ z : ℂ, |z.re - (-115/128)| ≤ (1/128) → |z.im - (53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20943/10000)) (c'i := (63/125)) (r' := (111/5000)) (E := (1/10000)) (N := (9893/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (14021/10000)) (c'i := (-8631/10000)) (r' := (241/2500)) (E := (1/10000)) (N := (21541/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-15091/10000)) (c'i := (-11723/10000)) (r' := (409/1250)) (E := (1/10000)) (N := (3293/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18269/10000)) (c'i := (23931/5000)) (r' := (13591/10000)) (E := (1/10000)) (N := (1911/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5123/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd45 : ∀ z : ℂ, |z.re - (-115/128)| ≤ (1/128) → |z.im - (55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10537/5000)) (c'i := (4759/10000)) (r' := (223/10000)) (E := (1/10000)) (N := (249/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (14847/10000)) (c'i := (-3789/5000)) (r' := (971/10000)) (E := (1/10000)) (N := (4321/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10999/10000)) (c'i := (-5011/5000)) (r' := (417/1250)) (E := (1/10000)) (N := (1667/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12623/5000)) (c'i := (17263/5000)) (r' := (5527/5000)) (E := (1/10000)) (N := (14881/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (42771/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd46 : ∀ z : ℂ, |z.re - (-113/128)| ≤ (1/128) → |z.im - (53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21221/10000)) (c'i := (5169/10000)) (r' := (219/10000)) (E := (1/10000)) (N := (9751/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15061/10000)) (c'i := (-4729/5000)) (r' := (241/2500)) (E := (1/10000)) (N := (10921/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6781/5000)) (c'i := (-16009/10000)) (r' := (3527/10000)) (E := (1/10000)) (N := (3557/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4317/1250)) (c'i := (55903/10000)) (r' := (8031/5000)) (E := (1/10000)) (N := (10491/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6571/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd47 : ∀ z : ℂ, |z.re - (-113/128)| ≤ (1/128) → |z.im - (55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21353/10000)) (c'i := (4893/10000)) (r' := (11/500)) (E := (1/10000)) (N := (9819/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15901/10000)) (c'i := (-526/625)) (r' := (971/10000)) (E := (1/10000)) (N := (21907/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9099/10000)) (c'i := (-2857/2000)) (r' := (3593/10000)) (E := (1/10000)) (N := (17991/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-39427/10000)) (c'i := (9619/2500)) (r' := (13477/10000)) (E := (1/10000)) (N := (16937/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (55089/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd43 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd44 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd45 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd46 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd47 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd31 : ∀ z : ℂ, |z.re - (-29/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd32 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd37 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd42 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd43 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd49 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd50 : ∀ z : ℂ, |z.re - (-59/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (15/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd52 : ∀ z : ℂ, |z.re - (-115/128)| ≤ (1/128) → |z.im - (57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21211/10000)) (c'i := (2239/5000)) (r' := (9/400)) (E := (1/10000)) (N := (2507/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3137/2000)) (c'i := (-6517/10000)) (r' := (983/10000)) (E := (1/10000)) (N := (21679/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1389/2000)) (c'i := (-1991/2500)) (r' := (3441/10000)) (E := (1/10000)) (N := (8493/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28819/10000)) (c'i := (11771/5000)) (r' := (4233/5000)) (E := (1/10000)) (N := (10567/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9303/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd53 : ∀ z : ℂ, |z.re - (-115/128)| ≤ (1/128) → |z.im - (59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21353/10000)) (c'i := (2099/5000)) (r' := (113/5000)) (E := (1/10000)) (N := (5049/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (16533/10000)) (c'i := (-681/1250)) (r' := (991/10000)) (E := (1/10000)) (N := (10881/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1467/5000)) (c'i := (-2767/5000)) (r' := (1777/5000)) (E := (1/10000)) (N := (1088/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-14751/5000)) (c'i := (15727/10000)) (r' := (5723/10000)) (E := (1/10000)) (N := (783/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4179/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd54 : ∀ z : ℂ, |z.re - (-113/128)| ≤ (1/128) → |z.im - (57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21489/10000)) (c'i := (4617/10000)) (r' := (111/5000)) (E := (1/10000)) (N := (618/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8373/5000)) (c'i := (-7363/10000)) (r' := (983/10000)) (E := (1/10000)) (N := (1099/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4679/10000)) (c'i := (-609/500)) (r' := (1849/5000)) (E := (1/10000)) (N := (9147/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-19973/5000)) (c'i := (11939/5000)) (r' := (1103/1000)) (E := (1/10000)) (N := (1631/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23269/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd55 : ∀ z : ℂ, |z.re - (-113/128)| ≤ (1/128) → |z.im - (59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21631/10000)) (c'i := (2171/5000)) (r' := (223/10000)) (E := (1/10000)) (N := (249/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3521/2000)) (c'i := (-394/625)) (r' := (991/10000)) (E := (1/10000)) (N := (22063/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7/250)) (c'i := (-2429/2500)) (r' := (381/1000)) (E := (1/10000)) (N := (187/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9183/2500)) (c'i := (814/625)) (r' := (8869/10000)) (E := (1/10000)) (N := (9721/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9743/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd51 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd52 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd53 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd54 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd55 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd57 : ∀ z : ℂ, |z.re - (-115/128)| ≤ (1/128) → |z.im - (61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (57/64)) (dy := (15/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd58 : ∀ z : ℂ, |z.re - (-115/128)| ≤ (1/128) → |z.im - (63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (57/64)) (dy := (31/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd60 : ∀ z : ℂ, |z.re - (-227/256)| ≤ (1/256) → |z.im - (121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21671/10000)) (c'i := (2049/5000)) (r' := (113/10000)) (E := (1/10000)) (N := (10049/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1124/625)) (c'i := (-2641/5000)) (r' := (251/5000)) (E := (1/10000)) (N := (2757/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (563/2500)) (c'i := (-3259/5000)) (r' := (1911/10000)) (E := (1/10000)) (N := (2343/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-31041/10000)) (c'i := (1193/1250)) (r' := (1503/5000)) (E := (1/10000)) (N := (6897/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1299/400)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd61 : ∀ z : ℂ, |z.re - (-227/256)| ≤ (1/256) → |z.im - (123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (113/128)) (dy := (61/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd62 : ∀ z : ℂ, |z.re - (-225/256)| ≤ (1/256) → |z.im - (121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21809/10000)) (c'i := (1043/2500)) (r' := (7/625)) (E := (1/10000)) (N := (499/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18523/10000)) (c'i := (-5717/10000)) (r' := (501/10000)) (E := (1/10000)) (N := (4441/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1871/5000)) (c'i := (-8699/10000)) (r' := (1971/10000)) (E := (1/10000)) (N := (9693/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-33467/10000)) (c'i := (597/1000)) (r' := (4127/10000)) (E := (1/10000)) (N := (947/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6799/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd63 : ∀ z : ℂ, |z.re - (-225/256)| ≤ (1/256) → |z.im - (123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5471/2500)) (c'i := (2017/5000)) (r' := (113/10000)) (E := (1/10000)) (N := (10017/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4741/2500)) (c'i := (-647/1250)) (r' := (253/5000)) (E := (1/10000)) (N := (22253/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (374/625)) (c'i := (-447/625)) (r' := (2019/10000)) (E := (1/10000)) (N := (9829/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-14417/5000)) (c'i := (49/125)) (r' := (4179/10000)) (E := (1/10000)) (N := (4663/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29099/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd59 : ∀ z : ℂ, |z.re - (-113/128)| ≤ (1/128) → |z.im - (61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd60 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd61 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd62 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd63 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd64 : ∀ z : ℂ, |z.re - (-113/128)| ≤ (1/128) → |z.im - (63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (31/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd56 : ∀ z : ℂ, |z.re - (-57/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd57 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd58 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd59 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd64 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd48 : ∀ z : ℂ, |z.re - (-29/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd49 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd50 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd51 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd56 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd28 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd29 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd30 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd31 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd48 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd66 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5243/2500)) (c'i := (3867/5000)) (r' := (101/1250)) (E := (1/10000)) (N := (4447/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10701/10000)) (c'i := (-19959/10000)) (r' := (3683/10000)) (E := (1/10000)) (N := (22353/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-11137/2000)) (c'i := (-7559/2500)) (r' := (9029/5000)) (E := (1/10000)) (N := (22647/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15841/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd67 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10681/5000)) (c'i := (6679/10000)) (r' := (207/2500)) (E := (1/10000)) (N := (9111/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13873/10000)) (c'i := (-3211/2000)) (r' := (189/500)) (E := (1/10000)) (N := (11191/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3383/1000)) (c'i := (-16033/5000)) (r' := (17489/10000)) (E := (1/10000)) (N := (21219/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11653/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd68 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5497/2500)) (c'i := (1617/2000)) (r' := (189/2500)) (E := (1/10000)) (N := (519/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1451/1000)) (c'i := (-923/400)) (r' := (721/2000)) (E := (1/10000)) (N := (5857/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (27257/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd69 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11189/5000)) (c'i := (7109/10000)) (r' := (777/10000)) (E := (1/10000)) (N := (1067/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4431/2500)) (c'i := (-19337/10000)) (r' := (743/2000)) (E := (1/10000)) (N := (23481/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16639/5000)) (c'i := (-28033/5000)) (r' := (5223/2500)) (E := (1/10000)) (N := (26231/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32599/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd65 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd66 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd67 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd68 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd69 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd72 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21441/10000)) (c'i := (2883/5000)) (r' := (53/1250)) (E := (1/10000)) (N := (118/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15347/10000)) (c'i := (-6123/5000)) (r' := (119/625)) (E := (1/10000)) (N := (22203/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18743/10000)) (c'i := (-6277/2500)) (r' := (7849/10000)) (E := (1/10000)) (N := (3927/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7833/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd73 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4339/2000)) (c'i := (5229/10000)) (r' := (43/1000)) (E := (1/10000)) (N := (4787/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17033/10000)) (c'i := (-10209/10000)) (r' := (1941/10000)) (E := (1/10000)) (N := (22317/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-871/1000)) (c'i := (-11149/5000)) (r' := (506/625)) (E := (1/10000)) (N := (19859/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-34717/5000)) (c'i := (51323/10000)) (r' := (45363/10000)) (E := (1/10000)) (N := (23939/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (86343/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd74 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1373/625)) (c'i := (601/1000)) (r' := (103/2500)) (E := (1/10000)) (N := (9157/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17347/10000)) (c'i := (-6963/5000)) (r' := (1897/10000)) (E := (1/10000)) (N := (2847/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8301/5000)) (c'i := (-7167/2000)) (r' := (881/1000)) (E := (1/10000)) (N := (11123/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39493/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd75 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11111/5000)) (c'i := (5493/10000)) (r' := (209/5000)) (E := (1/10000)) (N := (4647/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2383/1250)) (c'i := (-11933/10000)) (r' := (387/2000)) (E := (1/10000)) (N := (22891/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1299/2500)) (c'i := (-16509/5000)) (r' := (9089/10000)) (E := (1/10000)) (N := (22491/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2089/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd71 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd72 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd73 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd74 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd75 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd78 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21763/10000)) (c'i := (4757/10000)) (r' := (109/5000)) (E := (1/10000)) (N := (9749/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (89/50)) (c'i := (-329/400)) (r' := (979/10000)) (E := (1/10000)) (N := (22277/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2381/10000)) (c'i := (-16801/10000)) (r' := (3941/10000)) (E := (1/10000)) (N := (19609/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-687/125)) (c'i := (20481/10000)) (r' := (2989/2000)) (E := (1/10000)) (N := (16969/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14663/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd79 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1369/625)) (c'i := (2243/5000)) (r' := (11/500)) (E := (1/10000)) (N := (9821/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9333/5000)) (c'i := (-1793/2500)) (r' := (991/10000)) (E := (1/10000)) (N := (22359/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1199/5000)) (c'i := (-2859/2000)) (r' := (4067/10000)) (E := (1/10000)) (N := (19997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1179/250)) (c'i := (703/1250)) (r' := (13459/10000)) (E := (1/10000)) (N := (2899/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23747/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd80 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22031/10000)) (c'i := (306/625)) (r' := (43/2000)) (E := (1/10000)) (N := (961/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18839/10000)) (c'i := (-9093/10000)) (r' := (489/5000)) (E := (1/10000)) (N := (22569/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-77/10000)) (c'i := (-21781/10000)) (r' := (4193/10000)) (E := (1/10000)) (N := (20919/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-74741/10000)) (c'i := (2563/2000)) (r' := (10023/5000)) (E := (1/10000)) (N := (10891/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (75831/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd81 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22173/10000)) (c'i := (463/1000)) (r' := (217/10000)) (E := (1/10000)) (N := (2421/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19721/10000)) (c'i := (-2013/2500)) (r' := (99/1000)) (E := (1/10000)) (N := (5663/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1277/2500)) (c'i := (-19279/10000)) (r' := (2161/5000)) (E := (1/10000)) (N := (10651/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-61859/10000)) (c'i := (-1443/2000)) (r' := (19129/10000)) (E := (1/10000)) (N := (3989/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31139/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd77 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd78 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd79 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd80 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd81 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd84 : ∀ z : ℂ, |z.re - (-223/256)| ≤ (1/256) → |z.im - (121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10973/5000)) (c'i := (849/2000)) (r' := (111/10000)) (E := (1/10000)) (N := (9911/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19061/10000)) (c'i := (-769/1250)) (r' := (499/10000)) (E := (1/10000)) (N := (22353/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5247/10000)) (c'i := (-10973/10000)) (r' := (2027/10000)) (E := (1/10000)) (N := (2003/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9147/2500)) (c'i := (193/2000)) (r' := (5349/10000)) (E := (1/10000)) (N := (12163/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (183/50)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd85 : ∀ z : ℂ, |z.re - (-223/256)| ≤ (1/256) → |z.im - (123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1101/500)) (c'i := (4109/10000)) (r' := (7/625)) (E := (1/10000)) (N := (9949/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (39/20)) (c'i := (-351/625)) (r' := (101/2000)) (E := (1/10000)) (N := (22401/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7571/10000)) (c'i := (-4711/5000)) (r' := (2079/10000)) (E := (1/10000)) (N := (20293/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6089/2000)) (c'i := (-1787/10000)) (r' := (1093/2000)) (E := (1/10000)) (N := (12087/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30497/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd86 : ∀ z : ℂ, |z.re - (-221/256)| ≤ (1/256) → |z.im - (121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22081/10000)) (c'i := (4319/10000)) (r' := (111/10000)) (E := (1/10000)) (N := (9843/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2449/1250)) (c'i := (-3297/5000)) (r' := (503/10000)) (E := (1/10000)) (N := (9/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6737/10000)) (c'i := (-6679/5000)) (r' := (2109/10000)) (E := (1/10000)) (N := (1292/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8121/2000)) (c'i := (-5519/10000)) (r' := (1691/2500)) (E := (1/10000)) (N := (14961/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (20489/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd87 : ∀ z : ℂ, |z.re - (-221/256)| ≤ (1/256) → |z.im - (123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5539/2500)) (c'i := (523/1250)) (r' := (111/10000)) (E := (1/10000)) (N := (247/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10019/5000)) (c'i := (-303/500)) (r' := (63/1250)) (E := (1/10000)) (N := (5637/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (459/500)) (c'i := (-5903/5000)) (r' := (2139/10000)) (E := (1/10000)) (N := (4187/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-32811/10000)) (c'i := (-2299/2500)) (r' := (429/625)) (E := (1/10000)) (N := (3739/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1363/400)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd83 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd84 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd85 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd86 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd87 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd90 : ∀ z : ℂ, |z.re - (-447/512)| ≤ (1/512) → |z.im - (249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22043/10000)) (c'i := (997/2500)) (r' := (57/10000)) (E := (1/10000)) (N := (4997/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19699/10000)) (c'i := (-5101/10000)) (r' := (257/10000)) (E := (1/10000)) (N := (22401/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8903/10000)) (c'i := (-7617/10000)) (r' := (211/2000)) (E := (1/10000)) (N := (20349/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3147/1250)) (c'i := (-1083/10000)) (r' := (647/2500)) (E := (1/10000)) (N := (11717/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17983/5000)) (c'i := (17933/10000)) (r' := (13729/10000)) (E := (1/10000)) (N := (63/25)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10047/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd92 : ∀ z : ℂ, |z.re - (-895/1024)| ≤ (1/1024) → |z.im - (501/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (447/512)) (dy := (125/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd93 : ∀ z : ℂ, |z.re - (-895/1024)| ≤ (1/1024) → |z.im - (503/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (447/512)) (dy := (251/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd94 : ∀ z : ℂ, |z.re - (-893/1024)| ≤ (1/1024) → |z.im - (501/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22089/10000)) (c'i := (3947/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3987/2000)) (c'i := (-4957/10000)) (r' := (33/2500)) (E := (1/10000)) (N := (22439/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9983/10000)) (c'i := (-1821/2500)) (r' := (273/5000)) (E := (1/10000)) (N := (20543/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-283/125)) (c'i := (-2063/10000)) (r' := (691/5000)) (E := (1/10000)) (N := (6179/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (23531/10000)) (c'i := (21821/10000)) (r' := (6483/10000)) (E := (1/10000)) (N := (11367/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32091/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd95 : ∀ z : ℂ, |z.re - (-893/1024)| ≤ (1/1024) → |z.im - (503/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5527/2500)) (c'i := (3913/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (10009/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4009/2000)) (c'i := (-2411/5000)) (r' := (33/2500)) (E := (1/10000)) (N := (5613/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2111/2000)) (c'i := (-6851/10000)) (r' := (137/2500)) (E := (1/10000)) (N := (20617/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-20853/10000)) (c'i := (-991/5000)) (r' := (353/2500)) (E := (1/10000)) (N := (1573/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (987/625)) (c'i := (10373/5000)) (r' := (6123/10000)) (E := (1/10000)) (N := (5237/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-45401/10000)) (c'i := (19501/2500)) (r' := (7143/2000)) (E := (1/10000)) (N := (26073/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (45127/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd91 : ∀ z : ℂ, |z.re - (-447/512)| ≤ (1/512) → |z.im - (251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd92 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd93 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd94 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd95 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd96 : ∀ z : ℂ, |z.re - (-445/512)| ≤ (1/512) → |z.im - (249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22111/10000)) (c'i := (2013/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (249/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19969/10000)) (c'i := (-1331/2500)) (r' := (129/5000)) (E := (1/10000)) (N := (899/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4871/5000)) (c'i := (-8783/10000)) (r' := (269/2500)) (E := (1/10000)) (N := (20667/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-25523/10000)) (c'i := (-4633/10000)) (r' := (2943/10000)) (E := (1/10000)) (N := (13117/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2231/625)) (c'i := (3613/1000)) (r' := (16153/10000)) (E := (1/10000)) (N := (25941/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (50789/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd97 : ∀ z : ℂ, |z.re - (-445/512)| ≤ (1/512) → |z.im - (251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22149/10000)) (c'i := (1979/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (9979/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20191/10000)) (c'i := (-5053/10000)) (r' := (259/10000)) (E := (1/10000)) (N := (9/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5457/5000)) (c'i := (-317/400)) (r' := (1087/10000)) (E := (1/10000)) (N := (10407/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21669/10000)) (c'i := (-4819/10000)) (r' := (611/2000)) (E := (1/10000)) (N := (843/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4333/2500)) (c'i := (6673/2000)) (r' := (14513/10000)) (E := (1/10000)) (N := (22199/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (18799/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd89 : ∀ z : ℂ, |z.re - (-223/256)| ≤ (1/256) → |z.im - (125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd90 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd91 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd96 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd97 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd99 : ∀ z : ℂ, |z.re - (-447/512)| ≤ (1/512) → |z.im - (253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (223/256)) (dy := (63/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd100 : ∀ z : ℂ, |z.re - (-447/512)| ≤ (1/512) → |z.im - (255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (223/256)) (dy := (127/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd102 : ∀ z : ℂ, |z.re - (-891/1024)| ≤ (1/1024) → |z.im - (505/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22161/10000)) (c'i := (1949/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (5001/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5073/2500)) (c'i := (-4797/10000)) (r' := (33/2500)) (E := (1/10000)) (N := (11251/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (463/400)) (c'i := (-1747/2500)) (r' := (277/5000)) (E := (1/10000)) (N := (5213/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3757/2000)) (c'i := (-3697/10000)) (r' := (383/2500)) (E := (1/10000)) (N := (13521/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6621/10000)) (c'i := (2637/1000)) (r' := (6109/10000)) (E := (1/10000)) (N := (9573/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-46227/5000)) (c'i := (47399/10000)) (r' := (3699/1000)) (E := (1/10000)) (N := (27189/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12987/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd103 : ∀ z : ℂ, |z.re - (-891/1024)| ≤ (1/1024) → |z.im - (507/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1109/500)) (c'i := (483/1250)) (r' := (29/10000)) (E := (1/10000)) (N := (2503/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10201/5000)) (c'i := (-4661/10000)) (r' := (33/2500)) (E := (1/10000)) (N := (4503/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1519/1250)) (c'i := (-6539/10000)) (r' := (139/2500)) (E := (1/10000)) (N := (1308/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16809/10000)) (c'i := (-853/2500)) (r' := (1569/10000)) (E := (1/10000)) (N := (69/50)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21/1000)) (c'i := (479/200)) (r' := (1409/2500)) (E := (1/10000)) (N := (1072/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5291/625)) (c'i := (5737/5000)) (r' := (15103/5000)) (E := (1/10000)) (N := (23951/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (85429/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd104 : ∀ z : ℂ, |z.re - (-889/1024)| ≤ (1/1024) → |z.im - (505/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4439/2000)) (c'i := (3917/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (1997/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5107/2500)) (c'i := (-1227/2500)) (r' := (33/2500)) (E := (1/10000)) (N := (22539/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12021/10000)) (c'i := (-1893/2500)) (r' := (279/5000)) (E := (1/10000)) (N := (2101/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18583/10000)) (c'i := (-229/400)) (r' := (81/500)) (E := (1/10000)) (N := (888/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (791/2000)) (c'i := (16879/5000)) (r' := (6571/10000)) (E := (1/10000)) (N := (3889/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (8497/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd105 : ∀ z : ℂ, |z.re - (-889/1024)| ≤ (1/1024) → |z.im - (507/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11107/5000)) (c'i := (3883/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (1999/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10269/5000)) (c'i := (-4771/10000)) (r' := (133/10000)) (E := (1/10000)) (N := (22551/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2521/2000)) (c'i := (-7117/10000)) (r' := (113/2000)) (E := (1/10000)) (N := (4217/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16477/10000)) (c'i := (-2731/5000)) (r' := (1671/10000)) (E := (1/10000)) (N := (3619/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1567/5000)) (c'i := (30479/10000)) (r' := (761/1250)) (E := (1/10000)) (N := (17359/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30639/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd101 : ∀ z : ℂ, |z.re - (-445/512)| ≤ (1/512) → |z.im - (253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd102 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd103 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd104 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd105 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd107 : ∀ z : ℂ, |z.re - (-891/1024)| ≤ (1/1024) → |z.im - (509/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (445/512)) (dy := (127/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd108 : ∀ z : ℂ, |z.re - (-891/1024)| ≤ (1/1024) → |z.im - (511/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (445/512)) (dy := (255/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd109 : ∀ z : ℂ, |z.re - (-889/1024)| ≤ (1/1024) → |z.im - (509/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11117/5000)) (c'i := (3849/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (2501/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10327/5000)) (c'i := (-1159/2500)) (r' := (133/10000)) (E := (1/10000)) (N := (4513/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1321/1000)) (c'i := (-667/1000)) (r' := (567/10000)) (E := (1/10000)) (N := (1323/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7149/5000)) (c'i := (-2571/5000)) (r' := (857/5000)) (E := (1/10000)) (N := (14799/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9501/10000)) (c'i := (1699/625)) (r' := (551/1000)) (E := (1/10000)) (N := (3039/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7199/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd110 : ∀ z : ℂ, |z.re - (-889/1024)| ≤ (1/1024) → |z.im - (511/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (111/128)) (dy := (255/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd106 : ∀ z : ℂ, |z.re - (-445/512)| ≤ (1/512) → |z.im - (255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd107 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd108 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd109 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd110 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd98 : ∀ z : ℂ, |z.re - (-223/256)| ≤ (1/256) → |z.im - (127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd99 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd100 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd101 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd106 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd112 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22179/10000)) (c'i := (254/625)) (r' := (7/1250)) (E := (1/10000)) (N := (4963/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20239/10000)) (c'i := (-5547/10000)) (r' := (51/2000)) (E := (1/10000)) (N := (22549/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2117/2000)) (c'i := (-9973/10000)) (r' := (1079/10000)) (E := (1/10000)) (N := (10493/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-13021/5000)) (c'i := (-8633/10000)) (r' := (163/500)) (E := (1/10000)) (N := (909/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5487/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd113 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22217/10000)) (c'i := (3997/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (1989/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10231/5000)) (c'i := (-66/125)) (r' := (259/10000)) (E := (1/10000)) (N := (11287/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5891/5000)) (c'i := (-1141/1250)) (r' := (69/625)) (E := (1/10000)) (N := (21133/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-87/40)) (c'i := (-9029/10000)) (r' := (1709/5000)) (E := (1/10000)) (N := (2981/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5927/5000)) (c'i := (12939/2500)) (r' := (8643/5000)) (E := (1/10000)) (N := (471/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6637/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd114 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11123/5000)) (c'i := (2051/5000)) (r' := (7/1250)) (E := (1/10000)) (N := (2473/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10253/5000)) (c'i := (-5771/10000)) (r' := (51/2000)) (E := (1/10000)) (N := (11311/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11419/10000)) (c'i := (-2797/2500)) (r' := (137/1250)) (E := (1/10000)) (N := (21303/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-13389/5000)) (c'i := (-13071/10000)) (r' := (363/1000)) (E := (1/10000)) (N := (15987/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29797/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd115 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5571/2500)) (c'i := (807/2000)) (r' := (7/1250)) (E := (1/10000)) (N := (9911/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2073/1000)) (c'i := (-5503/10000)) (r' := (16/625)) (E := (1/10000)) (N := (22647/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2529/2000)) (c'i := (-2067/2000)) (r' := (1107/10000)) (E := (1/10000)) (N := (21449/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2749/1250)) (c'i := (-13657/10000)) (r' := (234/625)) (E := (1/10000)) (N := (4083/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2413/10000)) (c'i := (72549/10000)) (r' := (20809/10000)) (E := (1/10000)) (N := (1618/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (72589/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd111 : ∀ z : ℂ, |z.re - (-221/256)| ≤ (1/256) → |z.im - (125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd112 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd113 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd114 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd115 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd117 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4451/2000)) (c'i := (3929/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (2491/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4137/2000)) (c'i := (-313/625)) (r' := (13/500)) (E := (1/10000)) (N := (113/50)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12979/10000)) (c'i := (-4119/5000)) (r' := (279/2500)) (E := (1/10000)) (N := (21283/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17241/10000)) (c'i := (-1113/1250)) (r' := (3561/10000)) (E := (1/10000)) (N := (15373/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5503/10000)) (c'i := (43183/10000)) (r' := (3021/2000)) (E := (1/10000)) (N := (3881/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10883/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd118 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11147/5000)) (c'i := (3861/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (624/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1307/625)) (c'i := (-947/2000)) (r' := (13/500)) (E := (1/10000)) (N := (11313/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (14189/10000)) (c'i := (-1831/2500)) (r' := (281/2500)) (E := (1/10000)) (N := (10721/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12531/10000)) (c'i := (-519/625)) (r' := (3721/10000)) (E := (1/10000)) (N := (998/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18493/10000)) (c'i := (33291/10000)) (r' := (6293/5000)) (E := (1/10000)) (N := (15033/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (19041/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd119 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22323/10000)) (c'i := (248/625)) (r' := (57/10000)) (E := (1/10000)) (N := (9931/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20957/10000)) (c'i := (-1309/2500)) (r' := (261/10000)) (E := (1/10000)) (N := (22673/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6939/5000)) (c'i := (-4733/5000)) (r' := (1137/10000)) (E := (1/10000)) (N := (10801/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17001/10000)) (c'i := (-6897/5000)) (r' := (791/2000)) (E := (1/10000)) (N := (16799/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1089/625)) (c'i := (29691/5000)) (r' := (18903/10000)) (E := (1/10000)) (N := (10947/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12377/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd120 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11181/5000)) (c'i := (39/100)) (r' := (57/10000)) (E := (1/10000)) (N := (199/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4237/2000)) (c'i := (-2481/5000)) (r' := (261/10000)) (E := (1/10000)) (N := (227/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7559/5000)) (c'i := (-534/625)) (r' := (229/2000)) (E := (1/10000)) (N := (21759/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2349/2000)) (c'i := (-6677/5000)) (r' := (2057/5000)) (E := (1/10000)) (N := (8683/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-15669/5000)) (c'i := (43849/10000)) (r' := (2043/1250)) (E := (1/10000)) (N := (3557/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6737/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd116 : ∀ z : ℂ, |z.re - (-221/256)| ≤ (1/256) → |z.im - (127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd117 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd118 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd119 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd120 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd88 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd89 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd98 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd111 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd116 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd121 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-279/125)) (c'i := (1091/2500)) (r' := (219/10000)) (E := (1/10000)) (N := (9759/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10307/5000)) (c'i := (-7001/10000)) (r' := (1003/10000)) (E := (1/10000)) (N := (22743/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2573/2500)) (c'i := (-1024/625)) (r' := (2237/5000)) (E := (1/10000)) (N := (21771/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-43551/10000)) (c'i := (-4249/2000)) (r' := (2417/1250)) (E := (1/10000)) (N := (19349/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6057/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd123 : ∀ z : ℂ, |z.re - (-219/256)| ≤ (1/256) → |z.im - (125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11183/5000)) (c'i := (2063/5000)) (r' := (111/10000)) (E := (1/10000)) (N := (9851/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21021/10000)) (c'i := (-747/1250)) (r' := (127/2500)) (E := (1/10000)) (N := (2843/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13317/10000)) (c'i := (-3161/2500)) (r' := (9/40)) (E := (1/10000)) (N := (10927/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-25553/10000)) (c'i := (-5299/2500)) (r' := (439/500)) (E := (1/10000)) (N := (4591/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (33199/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd124 : ∀ z : ℂ, |z.re - (-219/256)| ≤ (1/256) → |z.im - (127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22443/10000)) (c'i := (499/1250)) (r' := (111/10000)) (E := (1/10000)) (N := (989/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (859/400)) (c'i := (-2719/5000)) (r' := (509/10000)) (E := (1/10000)) (N := (5699/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (793/500)) (c'i := (-2719/2500)) (r' := (457/2000)) (E := (1/10000)) (N := (22153/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-559/400)) (c'i := (-22019/10000)) (r' := (4661/5000)) (E := (1/10000)) (N := (19231/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28127/5000)) (c'i := (74023/10000)) (r' := (14343/2500)) (E := (1/10000)) (N := (326/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23243/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd125 : ∀ z : ℂ, |z.re - (-217/256)| ≤ (1/256) → |z.im - (125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22499/10000)) (c'i := (2101/5000)) (r' := (11/1000)) (E := (1/10000)) (N := (9783/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4311/2000)) (c'i := (-1607/2500)) (r' := (507/10000)) (E := (1/10000)) (N := (22889/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1503/1000)) (c'i := (-15231/10000)) (r' := (231/1000)) (E := (1/10000)) (N := (11247/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6977/2500)) (c'i := (-4163/1250)) (r' := (652/625)) (E := (1/10000)) (N := (21399/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (43451/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd126 : ∀ z : ℂ, |z.re - (-217/256)| ≤ (1/256) → |z.im - (127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1411/625)) (c'i := (407/1000)) (r' := (11/1000)) (E := (1/10000)) (N := (4911/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22011/10000)) (c'i := (-5897/10000)) (r' := (127/2500)) (E := (1/10000)) (N := (1147/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17671/10000)) (c'i := (-337/250)) (r' := (469/2000)) (E := (1/10000)) (N := (5697/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2849/2000)) (c'i := (-35161/10000)) (r' := (5493/5000)) (E := (1/10000)) (N := (11113/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2371/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd122 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd123 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd124 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd125 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd126 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd82 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd83 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd88 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd121 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd122 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd127 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4499/2000)) (c'i := (199/400)) (r' := (53/1250)) (E := (1/10000)) (N := (118/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20827/10000)) (c'i := (-9903/10000)) (r' := (79/400)) (E := (1/10000)) (N := (23039/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6269/10000)) (c'i := (-2877/1000)) (r' := (9511/10000)) (E := (1/10000)) (N := (11531/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-106141/10000)) (c'i := (-2949/1250)) (r' := (521/80)) (E := (1/10000)) (N := (14723/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (108731/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd129 : ∀ z : ℂ, |z.re - (-107/128)| ≤ (1/128) → |z.im - (61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22583/10000)) (c'i := (282/625)) (r' := (27/1250)) (E := (1/10000)) (N := (9623/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21663/10000)) (c'i := (-7899/10000)) (r' := (501/5000)) (E := (1/10000)) (N := (2303/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13389/10000)) (c'i := (-21743/10000)) (r' := (591/1250)) (E := (1/10000)) (N := (23059/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-56649/10000)) (c'i := (-45743/10000)) (r' := (26409/10000)) (E := (1/10000)) (N := (5107/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (72811/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd130 : ∀ z : ℂ, |z.re - (-107/128)| ≤ (1/128) → |z.im - (63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4547/2000)) (c'i := (4251/10000)) (r' := (217/10000)) (E := (1/10000)) (N := (9701/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22581/10000)) (c'i := (-6849/10000)) (r' := (1011/10000)) (E := (1/10000)) (N := (2313/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18999/10000)) (c'i := (-18451/10000)) (r' := (61/125)) (E := (1/10000)) (N := (23597/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1578/625)) (c'i := (-5763/1000)) (r' := (28261/10000)) (E := (1/10000)) (N := (5297/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (62917/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd131 : ∀ z : ℂ, |z.re - (-105/128)| ≤ (1/128) → |z.im - (61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11421/5000)) (c'i := (4661/10000)) (r' := (213/10000)) (E := (1/10000)) (N := (9487/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1457/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd132 : ∀ z : ℂ, |z.re - (-105/128)| ≤ (1/128) → |z.im - (63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22993/10000)) (c'i := (881/2000)) (r' := (107/5000)) (E := (1/10000)) (N := (9567/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23411/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd128 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd129 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd130 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd131 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd132 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd76 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd77 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd82 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd127 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd128 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd133 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22847/10000)) (c'i := (1533/2500)) (r' := (801/10000)) (E := (1/10000)) (N := (4403/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10569/5000)) (c'i := (-777/500)) (r' := (3859/10000)) (E := (1/10000)) (N := (2957/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-423/625)) (c'i := (-53217/10000)) (r' := (21761/10000)) (E := (1/10000)) (N := (6559/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10729/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd134 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11697/5000)) (c'i := (1289/2500)) (r' := (207/2500)) (E := (1/10000)) (N := (9111/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4791/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd70 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd71 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd76 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd133 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd134 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd18 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd19 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd28 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd65 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd70 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd135 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-471/200)) (c'i := (5459/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25957/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd136 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-62/25)) (c'i := (487/625)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5199/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd12 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd13 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd18 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd135 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd136 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd139 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd140 : ∀ z : ℂ, |z.re - (-15/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd145 : ∀ z : ℂ, |z.re - (-223/256)| ≤ (1/256) → |z.im - (129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (111/128)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd146 : ∀ z : ℂ, |z.re - (-223/256)| ≤ (1/256) → |z.im - (131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (111/128)) (dy := (65/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd148 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22333/10000)) (c'i := (1897/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (10003/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21137/10000)) (c'i := (-2233/5000)) (r' := (13/500)) (E := (1/10000)) (N := (22653/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15383/10000)) (c'i := (-16/25)) (r' := (1133/10000)) (E := (1/10000)) (N := (5401/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1933/2500)) (c'i := (-721/1000)) (r' := (3909/10000)) (E := (1/10000)) (N := (8331/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-663/250)) (c'i := (2363/1000)) (r' := (1961/2000)) (E := (1/10000)) (N := (10573/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (444/125)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd149 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22373/10000)) (c'i := (1863/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (10023/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21367/10000)) (c'i := (-262/625)) (r' := (261/10000)) (E := (1/10000)) (N := (11341/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8299/5000)) (c'i := (-2717/5000)) (r' := (573/5000)) (E := (1/10000)) (N := (871/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2703/10000)) (c'i := (-5559/10000)) (r' := (207/500)) (E := (1/10000)) (N := (3493/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1483/500)) (c'i := (3097/2000)) (r' := (6841/10000)) (E := (1/10000)) (N := (3091/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16729/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd150 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22401/10000)) (c'i := (3833/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (997/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21411/10000)) (c'i := (-4693/10000)) (r' := (261/10000)) (E := (1/10000)) (N := (22727/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (16341/10000)) (c'i := (-476/625)) (r' := (577/5000)) (E := (1/10000)) (N := (274/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3199/5000)) (c'i := (-12411/10000)) (r' := (43/100)) (E := (1/10000)) (N := (18029/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3861/1000)) (c'i := (28361/10000)) (r' := (13873/10000)) (E := (1/10000)) (N := (3491/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23953/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd151 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-561/250)) (c'i := (1883/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (9989/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21637/10000)) (c'i := (-2211/5000)) (r' := (261/10000)) (E := (1/10000)) (N := (11377/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17561/10000)) (c'i := (-416/625)) (r' := (581/5000)) (E := (1/10000)) (N := (4417/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-891/10000)) (c'i := (-10897/10000)) (r' := (2253/5000)) (E := (1/10000)) (N := (18781/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7819/2000)) (c'i := (7211/5000)) (r' := (5949/5000)) (E := (1/10000)) (N := (5467/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4167/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd147 : ∀ z : ℂ, |z.re - (-221/256)| ≤ (1/256) → |z.im - (129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd148 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd149 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd150 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd151 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd153 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (221/256)) (dy := (65/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd154 : ∀ z : ℂ, |z.re - (-443/512)| ≤ (1/512) → |z.im - (263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (221/256)) (dy := (131/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd156 : ∀ z : ℂ, |z.re - (-883/1024)| ≤ (1/1024) → |z.im - (521/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22453/10000)) (c'i := (741/2000)) (r' := (29/10000)) (E := (1/10000)) (N := (10013/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21741/10000)) (c'i := (-2079/5000)) (r' := (67/5000)) (E := (1/10000)) (N := (22757/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9119/5000)) (c'i := (-14/25)) (r' := (597/10000)) (E := (1/10000)) (N := (2767/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1413/5000)) (c'i := (-7947/10000)) (r' := (2317/10000)) (E := (1/10000)) (N := (19079/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-32817/10000)) (c'i := (1997/2500)) (r' := (1113/2500)) (E := (1/10000)) (N := (1687/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1351/400)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd157 : ∀ z : ℂ, |z.re - (-883/1024)| ≤ (1/1024) → |z.im - (523/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (441/512)) (dy := (261/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd158 : ∀ z : ℂ, |z.re - (-881/1024)| ≤ (1/1024) → |z.im - (521/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22487/10000)) (c'i := (149/400)) (r' := (29/10000)) (E := (1/10000)) (N := (2499/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21879/10000)) (c'i := (-4273/10000)) (r' := (67/5000)) (E := (1/10000)) (N := (11397/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18743/10000)) (c'i := (-3109/5000)) (r' := (601/10000)) (E := (1/10000)) (N := (22293/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (991/2500)) (c'i := (-10829/10000)) (r' := (1207/5000)) (E := (1/10000)) (N := (4937/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7491/2000)) (c'i := (779/2000)) (r' := (3079/5000)) (E := (1/10000)) (N := (2883/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4707/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd159 : ∀ z : ℂ, |z.re - (-881/1024)| ≤ (1/1024) → |z.im - (523/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22507/10000)) (c'i := (923/2500)) (r' := (29/10000)) (E := (1/10000)) (N := (5003/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21993/10000)) (c'i := (-4139/10000)) (r' := (67/5000)) (E := (1/10000)) (N := (2851/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4839/2500)) (c'i := (-2863/5000)) (r' := (151/2500)) (E := (1/10000)) (N := (1119/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6887/10000)) (c'i := (-4843/5000)) (r' := (2479/10000)) (E := (1/10000)) (N := (10093/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-31939/10000)) (c'i := (-861/10000)) (r' := (1303/2000)) (E := (1/10000)) (N := (2377/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (639/200)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd155 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd156 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd157 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd158 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd159 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd160 : ∀ z : ℂ, |z.re - (-441/512)| ≤ (1/512) → |z.im - (263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (131/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd152 : ∀ z : ℂ, |z.re - (-221/256)| ≤ (1/256) → |z.im - (131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd153 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd154 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd155 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd160 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd144 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (65/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd145 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd146 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd147 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd152 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd161 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (67/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (33/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd164 : ∀ z : ℂ, |z.re - (-439/512)| ≤ (1/512) → |z.im - (257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5617/2500)) (c'i := (242/625)) (r' := (57/10000)) (E := (1/10000)) (N := (621/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10841/5000)) (c'i := (-4919/10000)) (r' := (131/5000)) (E := (1/10000)) (N := (57/25)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17291/10000)) (c'i := (-8851/10000)) (r' := (47/400)) (E := (1/10000)) (N := (11117/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1309/2500)) (c'i := (-18129/10000)) (r' := (4709/10000)) (E := (1/10000)) (N := (777/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3589/625)) (c'i := (6293/2000)) (r' := (5003/2500)) (E := (1/10000)) (N := (18871/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (65479/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd165 : ∀ z : ℂ, |z.re - (-439/512)| ≤ (1/512) → |z.im - (259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22507/10000)) (c'i := (761/2000)) (r' := (57/10000)) (E := (1/10000)) (N := (2489/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21909/10000)) (c'i := (-581/1250)) (r' := (131/5000)) (E := (1/10000)) (N := (22827/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (927/500)) (c'i := (-7887/10000)) (r' := (1183/10000)) (E := (1/10000)) (N := (22397/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (853/10000)) (c'i := (-3353/2000)) (r' := (4913/10000)) (E := (1/10000)) (N := (5037/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-27667/5000)) (c'i := (481/500)) (r' := (18929/10000)) (E := (1/10000)) (N := (16787/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (56163/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd166 : ∀ z : ℂ, |z.re - (-437/512)| ≤ (1/512) → |z.im - (257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4507/2000)) (c'i := (489/1250)) (r' := (7/1250)) (E := (1/10000)) (N := (4951/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1372/625)) (c'i := (-5151/10000)) (r' := (129/5000)) (E := (1/10000)) (N := (22873/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4559/2500)) (c'i := (-2027/2000)) (r' := (1173/10000)) (E := (1/10000)) (N := (22549/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4317/10000)) (c'i := (-6121/2500)) (r' := (5039/10000)) (E := (1/10000)) (N := (1304/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-85383/10000)) (c'i := (33619/10000)) (r' := (3453/1250)) (E := (1/10000)) (N := (12431/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (91763/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd167 : ∀ z : ℂ, |z.re - (-437/512)| ≤ (1/512) → |z.im - (259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11287/5000)) (c'i := (769/2000)) (r' := (7/1250)) (E := (1/10000)) (N := (4961/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1109/500)) (c'i := (-4879/10000)) (r' := (259/10000)) (E := (1/10000)) (N := (229/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3903/2000)) (c'i := (-9163/10000)) (r' := (593/5000)) (E := (1/10000)) (N := (22711/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2387/10000)) (c'i := (-23283/10000)) (r' := (5261/10000)) (E := (1/10000)) (N := (539/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4047/500)) (c'i := (273/2000)) (r' := (1097/400)) (E := (1/10000)) (N := (11703/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (80951/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd163 : ∀ z : ℂ, |z.re - (-219/256)| ≤ (1/256) → |z.im - (129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd164 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd165 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd166 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd167 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd169 : ∀ z : ℂ, |z.re - (-439/512)| ≤ (1/512) → |z.im - (261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22547/10000)) (c'i := (1869/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (1247/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22139/10000)) (c'i := (-547/1250)) (r' := (263/10000)) (E := (1/10000)) (N := (4571/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19799/10000)) (c'i := (-431/625)) (r' := (1197/10000)) (E := (1/10000)) (N := (2821/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1429/2000)) (c'i := (-14827/10000)) (r' := (5169/10000)) (E := (1/10000)) (N := (10483/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-44179/10000)) (c'i := (-2177/2500)) (r' := (4927/2500)) (E := (1/10000)) (N := (16459/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11257/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd172 : ∀ z : ℂ, |z.re - (-1759/2048)| ≤ (1/2048) → |z.im - (1049/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22547/10000)) (c'i := (3681/10000)) (r' := (3/2000)) (E := (1/10000)) (N := (10001/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11091/5000)) (c'i := (-4119/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (11423/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20207/10000)) (c'i := (-2897/5000)) (r' := (159/5000)) (E := (1/10000)) (N := (11281/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (407/400)) (c'i := (-1367/1250)) (r' := (27/200)) (E := (1/10000)) (N := (10511/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28907/10000)) (c'i := (-391/400)) (r' := (4221/10000)) (E := (1/10000)) (N := (7469/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15257/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd173 : ∀ z : ℂ, |z.re - (-1759/2048)| ≤ (1/2048) → |z.im - (1051/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22557/10000)) (c'i := (733/2000)) (r' := (3/2000)) (E := (1/10000)) (N := (5003/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22239/10000)) (c'i := (-2027/5000)) (r' := (7/1000)) (E := (1/10000)) (N := (22853/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10257/5000)) (c'i := (-5551/10000)) (r' := (319/10000)) (E := (1/10000)) (N := (11303/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11701/10000)) (c'i := (-2059/2000)) (r' := (1369/10000)) (E := (1/10000)) (N := (5313/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-24207/10000)) (c'i := (-2903/2500)) (r' := (4461/10000)) (E := (1/10000)) (N := (7793/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8907/5000)) (c'i := (34349/5000)) (r' := (6493/2500)) (E := (1/10000)) (N := (26849/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7097/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd174 : ∀ z : ℂ, |z.re - (-1757/2048)| ≤ (1/2048) → |z.im - (1049/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22563/10000)) (c'i := (3691/10000)) (r' := (3/2000)) (E := (1/10000)) (N := (1249/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22247/10000)) (c'i := (-261/625)) (r' := (7/1000)) (E := (1/10000)) (N := (22863/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20449/10000)) (c'i := (-6101/10000)) (r' := (319/10000)) (E := (1/10000)) (N := (5659/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5397/5000)) (c'i := (-1559/1250)) (r' := (11/80)) (E := (1/10000)) (N := (1067/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7801/2500)) (c'i := (-2889/2000)) (r' := (4731/10000)) (E := (1/10000)) (N := (3299/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6877/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd175 : ∀ z : ℂ, |z.re - (-1757/2048)| ≤ (1/2048) → |z.im - (1051/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22573/10000)) (c'i := (147/400)) (r' := (3/2000)) (E := (1/10000)) (N := (9997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22303/10000)) (c'i := (-4111/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (22871/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1297/625)) (c'i := (-2929/5000)) (r' := (4/125)) (E := (1/10000)) (N := (22679/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12333/10000)) (c'i := (-11833/10000)) (r' := (1393/10000)) (E := (1/10000)) (N := (21563/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6523/2500)) (c'i := (-16707/10000)) (r' := (2481/5000)) (E := (1/10000)) (N := (4273/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15491/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd171 : ∀ z : ℂ, |z.re - (-879/1024)| ≤ (1/1024) → |z.im - (525/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd172 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd173 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd174 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd175 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd177 : ∀ z : ℂ, |z.re - (-1759/2048)| ≤ (1/2048) → |z.im - (1053/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (879/1024)) (dy := (263/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd178 : ∀ z : ℂ, |z.re - (-1759/2048)| ≤ (1/2048) → |z.im - (1055/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (879/1024)) (dy := (527/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd179 : ∀ z : ℂ, |z.re - (-1757/2048)| ≤ (1/2048) → |z.im - (1053/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2823/1250)) (c'i := (1829/5000)) (r' := (3/2000)) (E := (1/10000)) (N := (5001/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11183/5000)) (c'i := (-2021/5000)) (r' := (7/1000)) (E := (1/10000)) (N := (22879/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2109/1000)) (c'i := (-5601/10000)) (r' := (321/10000)) (E := (1/10000)) (N := (22729/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7021/5000)) (c'i := (-2229/2000)) (r' := (707/5000)) (E := (1/10000)) (N := (10911/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-20003/10000)) (c'i := (-941/500)) (r' := (5277/10000)) (E := (1/10000)) (N := (2241/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-22707/10000)) (c'i := (87771/10000)) (r' := (6361/2000)) (E := (1/10000)) (N := (5493/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4533/500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd180 : ∀ z : ℂ, |z.re - (-1757/2048)| ≤ (1/2048) → |z.im - (1055/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (439/512)) (dy := (527/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd176 : ∀ z : ℂ, |z.re - (-879/1024)| ≤ (1/1024) → |z.im - (527/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd177 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd178 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd179 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd180 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd181 : ∀ z : ℂ, |z.re - (-877/1024)| ≤ (1/1024) → |z.im - (525/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11297/5000)) (c'i := (1849/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (4991/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22381/10000)) (c'i := (-4231/10000)) (r' := (27/2000)) (E := (1/10000)) (N := (4579/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21001/10000)) (c'i := (-6459/10000)) (r' := (619/10000)) (E := (1/10000)) (N := (11389/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1579/1250)) (c'i := (-14649/10000)) (r' := (2763/10000)) (E := (1/10000)) (N := (5493/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-32803/10000)) (c'i := (-24529/10000)) (r' := (5733/5000)) (E := (1/10000)) (N := (1209/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (40959/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd182 : ∀ z : ℂ, |z.re - (-877/1024)| ≤ (1/1024) → |z.im - (527/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11307/5000)) (c'i := (733/2000)) (r' := (29/10000)) (E := (1/10000)) (N := (1249/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1406/625)) (c'i := (-256/625)) (r' := (27/2000)) (E := (1/10000)) (N := (2291/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21629/10000)) (c'i := (-5949/10000)) (r' := (621/10000)) (E := (1/10000)) (N := (11433/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7971/5000)) (c'i := (-6627/5000)) (r' := (2829/10000)) (E := (1/10000)) (N := (22433/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4863/2500)) (c'i := (-29779/10000)) (r' := (2509/2000)) (E := (1/10000)) (N := (20733/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-78141/10000)) (c'i := (32083/2500)) (r' := (105089/10000)) (E := (1/10000)) (N := (3557/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (601/40)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd170 : ∀ z : ℂ, |z.re - (-439/512)| ≤ (1/512) → |z.im - (263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd171 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd176 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd181 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd182 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd183 : ∀ z : ℂ, |z.re - (-437/512)| ≤ (1/512) → |z.im - (261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11307/5000)) (c'i := (1889/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (4971/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5603/2500)) (c'i := (-4607/10000)) (r' := (263/10000)) (E := (1/10000)) (N := (1433/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20807/10000)) (c'i := (-817/1000)) (r' := (1213/10000)) (E := (1/10000)) (N := (22881/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4659/5000)) (c'i := (-21519/10000)) (r' := (5577/10000)) (E := (1/10000)) (N := (11177/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16231/2500)) (c'i := (-27623/10000)) (r' := (29297/10000)) (E := (1/10000)) (N := (469/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14111/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd184 : ∀ z : ℂ, |z.re - (-437/512)| ≤ (1/512) → |z.im - (263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11327/5000)) (c'i := (3711/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (4981/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22643/10000)) (c'i := (-2167/5000)) (r' := (33/1250)) (E := (1/10000)) (N := (5739/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5523/2500)) (c'i := (-7147/10000)) (r' := (1227/10000)) (E := (1/10000)) (N := (4611/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8199/5000)) (c'i := (-9549/5000)) (r' := (366/625)) (E := (1/10000)) (N := (1161/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9221/2500)) (c'i := (-25077/5000)) (r' := (6589/2000)) (E := (1/10000)) (N := (6293/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (3891/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd168 : ∀ z : ℂ, |z.re - (-219/256)| ≤ (1/256) → |z.im - (131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd169 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd170 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd183 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd184 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd185 : ∀ z : ℂ, |z.re - (-217/256)| ≤ (1/256) → |z.im - (129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11327/5000)) (c'i := (3937/10000)) (r' := (111/10000)) (E := (1/10000)) (N := (4931/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2247/1000)) (c'i := (-2679/5000)) (r' := (257/5000)) (E := (1/10000)) (N := (11497/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20319/10000)) (c'i := (-11599/10000)) (r' := (481/2000)) (E := (1/10000)) (N := (23101/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (133/2500)) (c'i := (-2166/625)) (r' := (5923/5000)) (E := (1/10000)) (N := (23397/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9211/625)) (c'i := (8793/10000)) (r' := (96249/10000)) (E := (1/10000)) (N := (34661/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (147637/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd187 : ∀ z : ℂ, |z.re - (-435/512)| ≤ (1/512) → |z.im - (261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-567/250)) (c'i := (1909/5000)) (r' := (7/1250)) (E := (1/10000)) (N := (9909/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22681/10000)) (c'i := (-2419/5000)) (r' := (13/500)) (E := (1/10000)) (N := (23/10)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10901/5000)) (c'i := (-4733/5000)) (r' := (243/2000)) (E := (1/10000)) (N := (2899/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1409/1250)) (c'i := (-7199/2500)) (r' := (5931/10000)) (E := (1/10000)) (N := (23769/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30923/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd188 : ∀ z : ℂ, |z.re - (-435/512)| ≤ (1/512) → |z.im - (263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-284/125)) (c'i := (469/1250)) (r' := (57/10000)) (E := (1/10000)) (N := (9929/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1432/625)) (c'i := (-4569/10000)) (r' := (53/2000)) (E := (1/10000)) (N := (5757/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23363/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd189 : ∀ z : ℂ, |z.re - (-433/512)| ≤ (1/512) → |z.im - (261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11373/5000)) (c'i := (1929/5000)) (r' := (7/1250)) (E := (1/10000)) (N := (79/80)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (459/200)) (c'i := (-5071/10000)) (r' := (13/500)) (E := (1/10000)) (N := (23071/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23503/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd190 : ∀ z : ℂ, |z.re - (-433/512)| ≤ (1/512) → |z.im - (263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11393/5000)) (c'i := (237/625)) (r' := (7/1250)) (E := (1/10000)) (N := (1979/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23099/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd186 : ∀ z : ℂ, |z.re - (-217/256)| ≤ (1/256) → |z.im - (131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd187 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd188 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd189 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd190 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd162 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (65/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd163 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd168 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd185 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd186 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd194 : ∀ z : ℂ, |z.re - (-879/1024)| ≤ (1/1024) → |z.im - (529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (439/512)) (dy := (33/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd195 : ∀ z : ℂ, |z.re - (-879/1024)| ≤ (1/1024) → |z.im - (531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (439/512)) (dy := (265/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd197 : ∀ z : ℂ, |z.re - (-1755/2048)| ≤ (1/2048) → |z.im - (1057/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1131/500)) (c'i := (727/2000)) (r' := (3/2000)) (E := (1/10000)) (N := (2501/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4509/2000)) (c'i := (-793/2000)) (r' := (7/1000)) (E := (1/10000)) (N := (22911/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5489/2500)) (c'i := (-2699/5000)) (r' := (323/10000)) (E := (1/10000)) (N := (5723/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17993/10000)) (c'i := (-1403/1250)) (r' := (737/5000)) (E := (1/10000)) (N := (2261/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7523/10000)) (c'i := (-27911/10000)) (r' := (6477/10000)) (E := (1/10000)) (N := (21207/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-99543/10000)) (c'i := (2179/400)) (r' := (20843/5000)) (E := (1/10000)) (N := (7227/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (113473/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd198 : ∀ z : ℂ, |z.re - (-1755/2048)| ≤ (1/2048) → |z.im - (1059/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (877/1024)) (dy := (529/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd199 : ∀ z : ℂ, |z.re - (-1753/2048)| ≤ (1/2048) → |z.im - (1057/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22637/10000)) (c'i := (729/2000)) (r' := (3/2000)) (E := (1/10000)) (N := (2499/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4523/2000)) (c'i := (-2011/5000)) (r' := (7/1000)) (E := (1/10000)) (N := (22929/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11113/5000)) (c'i := (-357/625)) (r' := (81/2500)) (E := (1/10000)) (N := (2297/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18837/10000)) (c'i := (-12911/10000)) (r' := (1501/10000)) (E := (1/10000)) (N := (22949/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4243/5000)) (c'i := (-36161/10000)) (r' := (709/1000)) (E := (1/10000)) (N := (22837/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (37143/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd200 : ∀ z : ℂ, |z.re - (-1753/2048)| ≤ (1/2048) → |z.im - (1059/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22647/10000)) (c'i := (907/2500)) (r' := (3/2000)) (E := (1/10000)) (N := (10001/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1417/625)) (c'i := (-3953/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (2867/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22539/10000)) (c'i := (-1361/2500)) (r' := (13/400)) (E := (1/10000)) (N := (4603/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20537/10000)) (c'i := (-603/500)) (r' := (1521/10000)) (E := (1/10000)) (N := (5797/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (83/2500)) (c'i := (-7411/2000)) (r' := (1497/2000)) (E := (1/10000)) (N := (23817/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2316/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd196 : ∀ z : ℂ, |z.re - (-877/1024)| ≤ (1/1024) → |z.im - (529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd197 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd198 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd199 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd200 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd202 : ∀ z : ℂ, |z.re - (-1755/2048)| ≤ (1/2048) → |z.im - (1061/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (877/1024)) (dy := (265/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd203 : ∀ z : ℂ, |z.re - (-1755/2048)| ≤ (1/2048) → |z.im - (1063/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (877/1024)) (dy := (531/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd204 : ∀ z : ℂ, |z.re - (-1753/2048)| ≤ (1/2048) → |z.im - (1061/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22657/10000)) (c'i := (3611/10000)) (r' := (3/2000)) (E := (1/10000)) (N := (5003/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2273/1000)) (c'i := (-3883/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (22943/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11429/5000)) (c'i := (-1293/2500)) (r' := (13/400)) (E := (1/10000)) (N := (1153/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4687/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd205 : ∀ z : ℂ, |z.re - (-1753/2048)| ≤ (1/2048) → |z.im - (1063/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (219/256)) (dy := (531/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd201 : ∀ z : ℂ, |z.re - (-877/1024)| ≤ (1/1024) → |z.im - (531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd202 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd203 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd204 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd205 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd193 : ∀ z : ℂ, |z.re - (-439/512)| ≤ (1/512) → |z.im - (265/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd194 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd195 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd196 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd201 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd206 : ∀ z : ℂ, |z.re - (-439/512)| ≤ (1/512) → |z.im - (267/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (219/256)) (dy := (133/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd208 : ∀ z : ℂ, |z.re - (-875/1024)| ≤ (1/1024) → |z.im - (529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22667/10000)) (c'i := (3651/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (4993/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11373/5000)) (c'i := (-4071/10000)) (r' := (27/2000)) (E := (1/10000)) (N := (287/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22781/10000)) (c'i := (-151/250)) (r' := (157/2500)) (E := (1/10000)) (N := (5777/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20949/10000)) (c'i := (-15039/10000)) (r' := (751/2500)) (E := (1/10000)) (N := (23569/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6031/10000)) (c'i := (-5053/1000)) (r' := (8207/5000)) (E := (1/10000)) (N := (25789/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6361/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd209 : ∀ z : ℂ, |z.re - (-875/1024)| ≤ (1/1024) → |z.im - (531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22687/10000)) (c'i := (1809/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (2499/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22861/10000)) (c'i := (-246/625)) (r' := (27/2000)) (E := (1/10000)) (N := (11487/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23197/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd210 : ∀ z : ℂ, |z.re - (-873/1024)| ≤ (1/1024) → |z.im - (529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22701/10000)) (c'i := (459/1250)) (r' := (29/10000)) (E := (1/10000)) (N := (9969/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4577/2000)) (c'i := (-262/625)) (r' := (27/2000)) (E := (1/10000)) (N := (22997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4653/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd211 : ∀ z : ℂ, |z.re - (-873/1024)| ≤ (1/1024) → |z.im - (531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22721/10000)) (c'i := (1819/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (9979/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (23001/10000)) (c'i := (-1013/2500)) (r' := (27/2000)) (E := (1/10000)) (N := (23011/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4671/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd207 : ∀ z : ℂ, |z.re - (-437/512)| ≤ (1/512) → |z.im - (265/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd208 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd209 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd210 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd211 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd212 : ∀ z : ℂ, |z.re - (-437/512)| ≤ (1/512) → |z.im - (267/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4547/2000)) (c'i := (1789/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (10003/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5777/2500)) (c'i := (-3789/10000)) (r' := (33/1250)) (E := (1/10000)) (N := (4603/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2927/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd192 : ∀ z : ℂ, |z.re - (-219/256)| ≤ (1/256) → |z.im - (133/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd193 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd206 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd207 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd212 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd213 : ∀ z : ℂ, |z.re - (-219/256)| ≤ (1/256) → |z.im - (135/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22763/10000)) (c'i := (3457/10000)) (r' := (113/10000)) (E := (1/10000)) (N := (201/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (583/250)) (c'i := (-1629/5000)) (r' := (131/2500)) (E := (1/10000)) (N := (921/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (26021/10000)) (c'i := (-543/2000)) (r' := (2499/10000)) (E := (1/10000)) (N := (23547/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13081/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd214 : ∀ z : ℂ, |z.re - (-217/256)| ≤ (1/256) → |z.im - (133/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11407/5000)) (c'i := (459/1250)) (r' := (7/625)) (E := (1/10000)) (N := (9943/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (117/50)) (c'i := (-171/400)) (r' := (521/10000)) (E := (1/10000)) (N := (5777/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23787/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd215 : ∀ z : ℂ, |z.re - (-217/256)| ≤ (1/256) → |z.im - (135/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1431/625)) (c'i := (177/500)) (r' := (7/625)) (E := (1/10000)) (N := (624/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1448/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd191 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (67/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd192 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd213 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd214 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd215 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd143 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd144 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd161 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd162 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd191 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd217 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (17/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd218 : ∀ z : ℂ, |z.re - (-111/128)| ≤ (1/128) → |z.im - (71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd219 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11477/5000)) (c'i := (3299/10000)) (r' := (113/5000)) (E := (1/10000)) (N := (10079/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (243/100)) (c'i := (-533/2000)) (r' := (66/625)) (E := (1/10000)) (N := (2319/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4889/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd220 : ∀ z : ℂ, |z.re - (-109/128)| ≤ (1/128) → |z.im - (71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd216 : ∀ z : ℂ, |z.re - (-55/64)| ≤ (1/64) → |z.im - (35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd217 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd218 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd219 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd220 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd221 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23101/10000)) (c'i := (197/500)) (r' := (219/5000)) (E := (1/10000)) (N := (2439/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (24513/10000)) (c'i := (-1431/2500)) (r' := (519/2500)) (E := (1/10000)) (N := (4687/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6293/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd222 : ∀ z : ℂ, |z.re - (-53/64)| ≤ (1/64) → |z.im - (35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23433/10000)) (c'i := (1711/5000)) (r' := (223/5000)) (E := (1/10000)) (N := (397/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23681/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd142 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd143 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd216 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd221 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd222 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd223 : ∀ z : ℂ, |z.re - (-27/32)| ≤ (1/32) → |z.im - (19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11853/5000)) (c'i := (123/500)) (r' := (467/5000)) (E := (1/10000)) (N := (5159/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7073/2500)) (c'i := (817/10000)) (r' := (909/2000)) (E := (1/10000)) (N := (11917/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (28303/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd224 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-24019/10000)) (c'i := (4179/10000)) (r' := (857/10000)) (E := (1/10000)) (N := (1181/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24379/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd225 : ∀ z : ℂ, |z.re - (-25/32)| ≤ (1/32) → |z.im - (19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-12361/5000)) (c'i := (3203/10000)) (r' := (89/1000)) (E := (1/10000)) (N := (9813/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1558/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd141 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd142 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd223 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd224 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd225 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd226 : ∀ z : ℂ, |z.re - (-13/16)| ≤ (1/16) → |z.im - (11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1017/400)) (c'i := (327/2500)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12729/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd138 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd139 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd140 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd141 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd226 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd227 : ∀ z : ℂ, |z.re - (-7/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd228 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (1167/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1731/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd229 : ∀ z : ℂ, |z.re - (-5/8)| ≤ (1/8) → |z.im - (7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-621/200)) (c'i := (771/5000)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1943/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd137 : ∀ z : ℂ, |z.re - (-3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd138 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd227 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd228 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd229 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd230 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (1123/1000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29519/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd231 : ∀ z : ℂ, |z.re - (-1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-323/100)) (c'i := (873/1000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16729/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd11 : ∀ z : ℂ, |z.re - (-1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd12 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd137 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd230 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd231 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd233 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-323/100)) (c'i := (873/1000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16729/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd234 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (1123/1000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29519/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd236 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-621/200)) (c'i := (771/5000)) (r' := (2061/5000)) (E := (1/10000)) (N := (10753/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1943/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd237 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (1167/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1731/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd238 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-7/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (3/4)) (dy := (3/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd240 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1017/400)) (c'i := (327/2500)) (r' := (491/2500)) (E := (1/10000)) (N := (2661/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12729/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd242 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-12361/5000)) (c'i := (3203/10000)) (r' := (89/1000)) (E := (1/10000)) (N := (9813/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1558/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd243 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-24019/10000)) (c'i := (4179/10000)) (r' := (857/10000)) (E := (1/10000)) (N := (1181/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (24379/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd244 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-19/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11853/5000)) (c'i := (123/500)) (r' := (467/5000)) (E := (1/10000)) (N := (5159/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7073/2500)) (c'i := (817/10000)) (r' := (909/2000)) (E := (1/10000)) (N := (11917/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (28303/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd246 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23433/10000)) (c'i := (1711/5000)) (r' := (223/5000)) (E := (1/10000)) (N := (397/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23681/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd247 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-23101/10000)) (c'i := (197/500)) (r' := (219/5000)) (E := (1/10000)) (N := (2439/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (24513/10000)) (c'i := (-1431/2500)) (r' := (519/2500)) (E := (1/10000)) (N := (4687/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6293/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd249 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (27/32)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd250 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11477/5000)) (c'i := (3299/10000)) (r' := (113/5000)) (E := (1/10000)) (N := (10079/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (243/100)) (c'i := (-533/2000)) (r' := (66/625)) (E := (1/10000)) (N := (2319/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4889/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd251 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-71/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (35/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd252 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-69/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (17/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd248 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-35/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd249 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd250 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd251 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd252 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd255 : ∀ z : ℂ, |z.re - (217/256)| ≤ (1/256) → |z.im - (-135/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1431/625)) (c'i := (177/500)) (r' := (7/625)) (E := (1/10000)) (N := (624/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1448/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd256 : ∀ z : ℂ, |z.re - (217/256)| ≤ (1/256) → |z.im - (-133/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11407/5000)) (c'i := (459/1250)) (r' := (7/625)) (E := (1/10000)) (N := (9943/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (117/50)) (c'i := (-171/400)) (r' := (521/10000)) (E := (1/10000)) (N := (5777/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23787/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd257 : ∀ z : ℂ, |z.re - (219/256)| ≤ (1/256) → |z.im - (-135/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22763/10000)) (c'i := (3457/10000)) (r' := (113/10000)) (E := (1/10000)) (N := (201/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (583/250)) (c'i := (-1629/5000)) (r' := (131/2500)) (E := (1/10000)) (N := (921/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (26021/10000)) (c'i := (-543/2000)) (r' := (2499/10000)) (E := (1/10000)) (N := (23547/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13081/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd259 : ∀ z : ℂ, |z.re - (437/512)| ≤ (1/512) → |z.im - (-267/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4547/2000)) (c'i := (1789/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (10003/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5777/2500)) (c'i := (-3789/10000)) (r' := (33/1250)) (E := (1/10000)) (N := (4603/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2927/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd261 : ∀ z : ℂ, |z.re - (873/1024)| ≤ (1/1024) → |z.im - (-531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22721/10000)) (c'i := (1819/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (9979/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (23001/10000)) (c'i := (-1013/2500)) (r' := (27/2000)) (E := (1/10000)) (N := (23011/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4671/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd262 : ∀ z : ℂ, |z.re - (873/1024)| ≤ (1/1024) → |z.im - (-529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22701/10000)) (c'i := (459/1250)) (r' := (29/10000)) (E := (1/10000)) (N := (9969/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4577/2000)) (c'i := (-262/625)) (r' := (27/2000)) (E := (1/10000)) (N := (22997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4653/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd263 : ∀ z : ℂ, |z.re - (875/1024)| ≤ (1/1024) → |z.im - (-531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22687/10000)) (c'i := (1809/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (2499/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22861/10000)) (c'i := (-246/625)) (r' := (27/2000)) (E := (1/10000)) (N := (11487/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23197/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd264 : ∀ z : ℂ, |z.re - (875/1024)| ≤ (1/1024) → |z.im - (-529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22667/10000)) (c'i := (3651/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (4993/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11373/5000)) (c'i := (-4071/10000)) (r' := (27/2000)) (E := (1/10000)) (N := (287/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22781/10000)) (c'i := (-151/250)) (r' := (157/2500)) (E := (1/10000)) (N := (5777/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20949/10000)) (c'i := (-15039/10000)) (r' := (751/2500)) (E := (1/10000)) (N := (23569/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6031/10000)) (c'i := (-5053/1000)) (r' := (8207/5000)) (E := (1/10000)) (N := (25789/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6361/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd260 : ∀ z : ℂ, |z.re - (437/512)| ≤ (1/512) → |z.im - (-265/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd261 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd262 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd263 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd264 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd265 : ∀ z : ℂ, |z.re - (439/512)| ≤ (1/512) → |z.im - (-267/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (219/256)) (dy := (133/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd268 : ∀ z : ℂ, |z.re - (1753/2048)| ≤ (1/2048) → |z.im - (-1063/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (219/256)) (dy := (531/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd269 : ∀ z : ℂ, |z.re - (1753/2048)| ≤ (1/2048) → |z.im - (-1061/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22657/10000)) (c'i := (3611/10000)) (r' := (3/2000)) (E := (1/10000)) (N := (5003/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2273/1000)) (c'i := (-3883/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (22943/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11429/5000)) (c'i := (-1293/2500)) (r' := (13/400)) (E := (1/10000)) (N := (1153/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4687/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd270 : ∀ z : ℂ, |z.re - (1755/2048)| ≤ (1/2048) → |z.im - (-1063/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (877/1024)) (dy := (531/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd271 : ∀ z : ℂ, |z.re - (1755/2048)| ≤ (1/2048) → |z.im - (-1061/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (877/1024)) (dy := (265/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd267 : ∀ z : ℂ, |z.re - (877/1024)| ≤ (1/1024) → |z.im - (-531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd268 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd269 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd270 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd271 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd273 : ∀ z : ℂ, |z.re - (1753/2048)| ≤ (1/2048) → |z.im - (-1059/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22647/10000)) (c'i := (907/2500)) (r' := (3/2000)) (E := (1/10000)) (N := (10001/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1417/625)) (c'i := (-3953/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (2867/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22539/10000)) (c'i := (-1361/2500)) (r' := (13/400)) (E := (1/10000)) (N := (4603/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20537/10000)) (c'i := (-603/500)) (r' := (1521/10000)) (E := (1/10000)) (N := (5797/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (83/2500)) (c'i := (-7411/2000)) (r' := (1497/2000)) (E := (1/10000)) (N := (23817/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2316/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd274 : ∀ z : ℂ, |z.re - (1753/2048)| ≤ (1/2048) → |z.im - (-1057/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22637/10000)) (c'i := (729/2000)) (r' := (3/2000)) (E := (1/10000)) (N := (2499/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4523/2000)) (c'i := (-2011/5000)) (r' := (7/1000)) (E := (1/10000)) (N := (22929/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11113/5000)) (c'i := (-357/625)) (r' := (81/2500)) (E := (1/10000)) (N := (2297/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18837/10000)) (c'i := (-12911/10000)) (r' := (1501/10000)) (E := (1/10000)) (N := (22949/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4243/5000)) (c'i := (-36161/10000)) (r' := (709/1000)) (E := (1/10000)) (N := (22837/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (37143/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd275 : ∀ z : ℂ, |z.re - (1755/2048)| ≤ (1/2048) → |z.im - (-1059/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (877/1024)) (dy := (529/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd276 : ∀ z : ℂ, |z.re - (1755/2048)| ≤ (1/2048) → |z.im - (-1057/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1131/500)) (c'i := (727/2000)) (r' := (3/2000)) (E := (1/10000)) (N := (2501/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4509/2000)) (c'i := (-793/2000)) (r' := (7/1000)) (E := (1/10000)) (N := (22911/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5489/2500)) (c'i := (-2699/5000)) (r' := (323/10000)) (E := (1/10000)) (N := (5723/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17993/10000)) (c'i := (-1403/1250)) (r' := (737/5000)) (E := (1/10000)) (N := (2261/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7523/10000)) (c'i := (-27911/10000)) (r' := (6477/10000)) (E := (1/10000)) (N := (21207/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-99543/10000)) (c'i := (2179/400)) (r' := (20843/5000)) (E := (1/10000)) (N := (7227/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (113473/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd272 : ∀ z : ℂ, |z.re - (877/1024)| ≤ (1/1024) → |z.im - (-529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd273 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd274 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd275 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd276 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd277 : ∀ z : ℂ, |z.re - (879/1024)| ≤ (1/1024) → |z.im - (-531/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (439/512)) (dy := (265/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd278 : ∀ z : ℂ, |z.re - (879/1024)| ≤ (1/1024) → |z.im - (-529/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (439/512)) (dy := (33/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd266 : ∀ z : ℂ, |z.re - (439/512)| ≤ (1/512) → |z.im - (-265/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd267 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd272 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd277 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd278 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd258 : ∀ z : ℂ, |z.re - (219/256)| ≤ (1/256) → |z.im - (-133/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd259 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd260 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd265 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd266 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd254 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-67/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd255 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd256 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd257 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd258 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd281 : ∀ z : ℂ, |z.re - (433/512)| ≤ (1/512) → |z.im - (-263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11393/5000)) (c'i := (237/625)) (r' := (7/1250)) (E := (1/10000)) (N := (1979/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23099/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd282 : ∀ z : ℂ, |z.re - (433/512)| ≤ (1/512) → |z.im - (-261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11373/5000)) (c'i := (1929/5000)) (r' := (7/1250)) (E := (1/10000)) (N := (79/80)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (459/200)) (c'i := (-5071/10000)) (r' := (13/500)) (E := (1/10000)) (N := (23071/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23503/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd283 : ∀ z : ℂ, |z.re - (435/512)| ≤ (1/512) → |z.im - (-263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-284/125)) (c'i := (469/1250)) (r' := (57/10000)) (E := (1/10000)) (N := (9929/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1432/625)) (c'i := (-4569/10000)) (r' := (53/2000)) (E := (1/10000)) (N := (5757/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23363/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd284 : ∀ z : ℂ, |z.re - (435/512)| ≤ (1/512) → |z.im - (-261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-567/250)) (c'i := (1909/5000)) (r' := (7/1250)) (E := (1/10000)) (N := (9909/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22681/10000)) (c'i := (-2419/5000)) (r' := (13/500)) (E := (1/10000)) (N := (23/10)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10901/5000)) (c'i := (-4733/5000)) (r' := (243/2000)) (E := (1/10000)) (N := (2899/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1409/1250)) (c'i := (-7199/2500)) (r' := (5931/10000)) (E := (1/10000)) (N := (23769/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30923/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd280 : ∀ z : ℂ, |z.re - (217/256)| ≤ (1/256) → |z.im - (-131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd281 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd282 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd283 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd284 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd285 : ∀ z : ℂ, |z.re - (217/256)| ≤ (1/256) → |z.im - (-129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11327/5000)) (c'i := (3937/10000)) (r' := (111/10000)) (E := (1/10000)) (N := (4931/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2247/1000)) (c'i := (-2679/5000)) (r' := (257/5000)) (E := (1/10000)) (N := (11497/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20319/10000)) (c'i := (-11599/10000)) (r' := (481/2000)) (E := (1/10000)) (N := (23101/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (133/2500)) (c'i := (-2166/625)) (r' := (5923/5000)) (E := (1/10000)) (N := (23397/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9211/625)) (c'i := (8793/10000)) (r' := (96249/10000)) (E := (1/10000)) (N := (34661/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (147637/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd287 : ∀ z : ℂ, |z.re - (437/512)| ≤ (1/512) → |z.im - (-263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11327/5000)) (c'i := (3711/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (4981/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22643/10000)) (c'i := (-2167/5000)) (r' := (33/1250)) (E := (1/10000)) (N := (5739/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5523/2500)) (c'i := (-7147/10000)) (r' := (1227/10000)) (E := (1/10000)) (N := (4611/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8199/5000)) (c'i := (-9549/5000)) (r' := (366/625)) (E := (1/10000)) (N := (1161/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9221/2500)) (c'i := (-25077/5000)) (r' := (6589/2000)) (E := (1/10000)) (N := (6293/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (3891/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd288 : ∀ z : ℂ, |z.re - (437/512)| ≤ (1/512) → |z.im - (-261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11307/5000)) (c'i := (1889/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (4971/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5603/2500)) (c'i := (-4607/10000)) (r' := (263/10000)) (E := (1/10000)) (N := (1433/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20807/10000)) (c'i := (-817/1000)) (r' := (1213/10000)) (E := (1/10000)) (N := (22881/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4659/5000)) (c'i := (-21519/10000)) (r' := (5577/10000)) (E := (1/10000)) (N := (11177/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16231/2500)) (c'i := (-27623/10000)) (r' := (29297/10000)) (E := (1/10000)) (N := (469/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14111/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd290 : ∀ z : ℂ, |z.re - (877/1024)| ≤ (1/1024) → |z.im - (-527/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11307/5000)) (c'i := (733/2000)) (r' := (29/10000)) (E := (1/10000)) (N := (1249/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1406/625)) (c'i := (-256/625)) (r' := (27/2000)) (E := (1/10000)) (N := (2291/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21629/10000)) (c'i := (-5949/10000)) (r' := (621/10000)) (E := (1/10000)) (N := (11433/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7971/5000)) (c'i := (-6627/5000)) (r' := (2829/10000)) (E := (1/10000)) (N := (22433/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4863/2500)) (c'i := (-29779/10000)) (r' := (2509/2000)) (E := (1/10000)) (N := (20733/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-78141/10000)) (c'i := (32083/2500)) (r' := (105089/10000)) (E := (1/10000)) (N := (3557/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (601/40)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd291 : ∀ z : ℂ, |z.re - (877/1024)| ≤ (1/1024) → |z.im - (-525/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11297/5000)) (c'i := (1849/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (4991/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22381/10000)) (c'i := (-4231/10000)) (r' := (27/2000)) (E := (1/10000)) (N := (4579/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21001/10000)) (c'i := (-6459/10000)) (r' := (619/10000)) (E := (1/10000)) (N := (11389/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1579/1250)) (c'i := (-14649/10000)) (r' := (2763/10000)) (E := (1/10000)) (N := (5493/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-32803/10000)) (c'i := (-24529/10000)) (r' := (5733/5000)) (E := (1/10000)) (N := (1209/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (40959/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd293 : ∀ z : ℂ, |z.re - (1757/2048)| ≤ (1/2048) → |z.im - (-1055/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (439/512)) (dy := (527/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd294 : ∀ z : ℂ, |z.re - (1757/2048)| ≤ (1/2048) → |z.im - (-1053/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2823/1250)) (c'i := (1829/5000)) (r' := (3/2000)) (E := (1/10000)) (N := (5001/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11183/5000)) (c'i := (-2021/5000)) (r' := (7/1000)) (E := (1/10000)) (N := (22879/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2109/1000)) (c'i := (-5601/10000)) (r' := (321/10000)) (E := (1/10000)) (N := (22729/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7021/5000)) (c'i := (-2229/2000)) (r' := (707/5000)) (E := (1/10000)) (N := (10911/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-20003/10000)) (c'i := (-941/500)) (r' := (5277/10000)) (E := (1/10000)) (N := (2241/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-22707/10000)) (c'i := (87771/10000)) (r' := (6361/2000)) (E := (1/10000)) (N := (5493/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4533/500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd295 : ∀ z : ℂ, |z.re - (1759/2048)| ≤ (1/2048) → |z.im - (-1055/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (879/1024)) (dy := (527/1024)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd296 : ∀ z : ℂ, |z.re - (1759/2048)| ≤ (1/2048) → |z.im - (-1053/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (879/1024)) (dy := (263/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd292 : ∀ z : ℂ, |z.re - (879/1024)| ≤ (1/1024) → |z.im - (-527/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd293 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd294 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd295 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd296 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd298 : ∀ z : ℂ, |z.re - (1757/2048)| ≤ (1/2048) → |z.im - (-1051/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22573/10000)) (c'i := (147/400)) (r' := (3/2000)) (E := (1/10000)) (N := (9997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22303/10000)) (c'i := (-4111/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (22871/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1297/625)) (c'i := (-2929/5000)) (r' := (4/125)) (E := (1/10000)) (N := (22679/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12333/10000)) (c'i := (-11833/10000)) (r' := (1393/10000)) (E := (1/10000)) (N := (21563/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6523/2500)) (c'i := (-16707/10000)) (r' := (2481/5000)) (E := (1/10000)) (N := (4273/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15491/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd299 : ∀ z : ℂ, |z.re - (1757/2048)| ≤ (1/2048) → |z.im - (-1049/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22563/10000)) (c'i := (3691/10000)) (r' := (3/2000)) (E := (1/10000)) (N := (1249/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22247/10000)) (c'i := (-261/625)) (r' := (7/1000)) (E := (1/10000)) (N := (22863/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20449/10000)) (c'i := (-6101/10000)) (r' := (319/10000)) (E := (1/10000)) (N := (5659/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5397/5000)) (c'i := (-1559/1250)) (r' := (11/80)) (E := (1/10000)) (N := (1067/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7801/2500)) (c'i := (-2889/2000)) (r' := (4731/10000)) (E := (1/10000)) (N := (3299/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6877/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd300 : ∀ z : ℂ, |z.re - (1759/2048)| ≤ (1/2048) → |z.im - (-1051/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22557/10000)) (c'i := (733/2000)) (r' := (3/2000)) (E := (1/10000)) (N := (5003/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22239/10000)) (c'i := (-2027/5000)) (r' := (7/1000)) (E := (1/10000)) (N := (22853/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10257/5000)) (c'i := (-5551/10000)) (r' := (319/10000)) (E := (1/10000)) (N := (11303/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11701/10000)) (c'i := (-2059/2000)) (r' := (1369/10000)) (E := (1/10000)) (N := (5313/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-24207/10000)) (c'i := (-2903/2500)) (r' := (4461/10000)) (E := (1/10000)) (N := (7793/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8907/5000)) (c'i := (34349/5000)) (r' := (6493/2500)) (E := (1/10000)) (N := (26849/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7097/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd301 : ∀ z : ℂ, |z.re - (1759/2048)| ≤ (1/2048) → |z.im - (-1049/2048)| ≤ (1/2048) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22547/10000)) (c'i := (3681/10000)) (r' := (3/2000)) (E := (1/10000)) (N := (10001/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11091/5000)) (c'i := (-4119/10000)) (r' := (7/1000)) (E := (1/10000)) (N := (11423/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20207/10000)) (c'i := (-2897/5000)) (r' := (159/5000)) (E := (1/10000)) (N := (11281/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (407/400)) (c'i := (-1367/1250)) (r' := (27/200)) (E := (1/10000)) (N := (10511/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28907/10000)) (c'i := (-391/400)) (r' := (4221/10000)) (E := (1/10000)) (N := (7469/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15257/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd297 : ∀ z : ℂ, |z.re - (879/1024)| ≤ (1/1024) → |z.im - (-525/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd298 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd299 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd300 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd301 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd289 : ∀ z : ℂ, |z.re - (439/512)| ≤ (1/512) → |z.im - (-263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd290 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd291 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd292 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd297 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd302 : ∀ z : ℂ, |z.re - (439/512)| ≤ (1/512) → |z.im - (-261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22547/10000)) (c'i := (1869/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (1247/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22139/10000)) (c'i := (-547/1250)) (r' := (263/10000)) (E := (1/10000)) (N := (4571/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19799/10000)) (c'i := (-431/625)) (r' := (1197/10000)) (E := (1/10000)) (N := (2821/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1429/2000)) (c'i := (-14827/10000)) (r' := (5169/10000)) (E := (1/10000)) (N := (10483/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-44179/10000)) (c'i := (-2177/2500)) (r' := (4927/2500)) (E := (1/10000)) (N := (16459/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11257/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd286 : ∀ z : ℂ, |z.re - (219/256)| ≤ (1/256) → |z.im - (-131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd287 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd288 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd289 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd302 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd304 : ∀ z : ℂ, |z.re - (437/512)| ≤ (1/512) → |z.im - (-259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11287/5000)) (c'i := (769/2000)) (r' := (7/1250)) (E := (1/10000)) (N := (4961/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1109/500)) (c'i := (-4879/10000)) (r' := (259/10000)) (E := (1/10000)) (N := (229/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3903/2000)) (c'i := (-9163/10000)) (r' := (593/5000)) (E := (1/10000)) (N := (22711/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2387/10000)) (c'i := (-23283/10000)) (r' := (5261/10000)) (E := (1/10000)) (N := (539/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4047/500)) (c'i := (273/2000)) (r' := (1097/400)) (E := (1/10000)) (N := (11703/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (80951/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd305 : ∀ z : ℂ, |z.re - (437/512)| ≤ (1/512) → |z.im - (-257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4507/2000)) (c'i := (489/1250)) (r' := (7/1250)) (E := (1/10000)) (N := (4951/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1372/625)) (c'i := (-5151/10000)) (r' := (129/5000)) (E := (1/10000)) (N := (22873/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4559/2500)) (c'i := (-2027/2000)) (r' := (1173/10000)) (E := (1/10000)) (N := (22549/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4317/10000)) (c'i := (-6121/2500)) (r' := (5039/10000)) (E := (1/10000)) (N := (1304/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-85383/10000)) (c'i := (33619/10000)) (r' := (3453/1250)) (E := (1/10000)) (N := (12431/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (91763/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd306 : ∀ z : ℂ, |z.re - (439/512)| ≤ (1/512) → |z.im - (-259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22507/10000)) (c'i := (761/2000)) (r' := (57/10000)) (E := (1/10000)) (N := (2489/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21909/10000)) (c'i := (-581/1250)) (r' := (131/5000)) (E := (1/10000)) (N := (22827/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (927/500)) (c'i := (-7887/10000)) (r' := (1183/10000)) (E := (1/10000)) (N := (22397/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (853/10000)) (c'i := (-3353/2000)) (r' := (4913/10000)) (E := (1/10000)) (N := (5037/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-27667/5000)) (c'i := (481/500)) (r' := (18929/10000)) (E := (1/10000)) (N := (16787/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (56163/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd307 : ∀ z : ℂ, |z.re - (439/512)| ≤ (1/512) → |z.im - (-257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5617/2500)) (c'i := (242/625)) (r' := (57/10000)) (E := (1/10000)) (N := (621/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10841/5000)) (c'i := (-4919/10000)) (r' := (131/5000)) (E := (1/10000)) (N := (57/25)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17291/10000)) (c'i := (-8851/10000)) (r' := (47/400)) (E := (1/10000)) (N := (11117/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1309/2500)) (c'i := (-18129/10000)) (r' := (4709/10000)) (E := (1/10000)) (N := (777/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3589/625)) (c'i := (6293/2000)) (r' := (5003/2500)) (E := (1/10000)) (N := (18871/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (65479/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd303 : ∀ z : ℂ, |z.re - (219/256)| ≤ (1/256) → |z.im - (-129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd304 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd305 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd306 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd307 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd279 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-65/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd280 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd285 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd286 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd303 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd308 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-67/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (33/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd311 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (55/64)) (dy := (131/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd313 : ∀ z : ℂ, |z.re - (881/1024)| ≤ (1/1024) → |z.im - (-523/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22507/10000)) (c'i := (923/2500)) (r' := (29/10000)) (E := (1/10000)) (N := (5003/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21993/10000)) (c'i := (-4139/10000)) (r' := (67/5000)) (E := (1/10000)) (N := (2851/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4839/2500)) (c'i := (-2863/5000)) (r' := (151/2500)) (E := (1/10000)) (N := (1119/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6887/10000)) (c'i := (-4843/5000)) (r' := (2479/10000)) (E := (1/10000)) (N := (10093/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-31939/10000)) (c'i := (-861/10000)) (r' := (1303/2000)) (E := (1/10000)) (N := (2377/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (639/200)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd314 : ∀ z : ℂ, |z.re - (881/1024)| ≤ (1/1024) → |z.im - (-521/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22487/10000)) (c'i := (149/400)) (r' := (29/10000)) (E := (1/10000)) (N := (2499/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21879/10000)) (c'i := (-4273/10000)) (r' := (67/5000)) (E := (1/10000)) (N := (11397/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18743/10000)) (c'i := (-3109/5000)) (r' := (601/10000)) (E := (1/10000)) (N := (22293/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (991/2500)) (c'i := (-10829/10000)) (r' := (1207/5000)) (E := (1/10000)) (N := (4937/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7491/2000)) (c'i := (779/2000)) (r' := (3079/5000)) (E := (1/10000)) (N := (2883/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4707/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd315 : ∀ z : ℂ, |z.re - (883/1024)| ≤ (1/1024) → |z.im - (-523/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (441/512)) (dy := (261/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd316 : ∀ z : ℂ, |z.re - (883/1024)| ≤ (1/1024) → |z.im - (-521/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22453/10000)) (c'i := (741/2000)) (r' := (29/10000)) (E := (1/10000)) (N := (10013/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21741/10000)) (c'i := (-2079/5000)) (r' := (67/5000)) (E := (1/10000)) (N := (22757/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9119/5000)) (c'i := (-14/25)) (r' := (597/10000)) (E := (1/10000)) (N := (2767/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1413/5000)) (c'i := (-7947/10000)) (r' := (2317/10000)) (E := (1/10000)) (N := (19079/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-32817/10000)) (c'i := (1997/2500)) (r' := (1113/2500)) (E := (1/10000)) (N := (1687/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1351/400)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd312 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd313 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd314 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd315 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd316 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd317 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-263/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (221/256)) (dy := (131/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd318 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-261/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (221/256)) (dy := (65/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd310 : ∀ z : ℂ, |z.re - (221/256)| ≤ (1/256) → |z.im - (-131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd311 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd312 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd317 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd318 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd320 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-561/250)) (c'i := (1883/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (9989/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21637/10000)) (c'i := (-2211/5000)) (r' := (261/10000)) (E := (1/10000)) (N := (11377/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17561/10000)) (c'i := (-416/625)) (r' := (581/5000)) (E := (1/10000)) (N := (4417/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-891/10000)) (c'i := (-10897/10000)) (r' := (2253/5000)) (E := (1/10000)) (N := (18781/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7819/2000)) (c'i := (7211/5000)) (r' := (5949/5000)) (E := (1/10000)) (N := (5467/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4167/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd321 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22401/10000)) (c'i := (3833/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (997/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21411/10000)) (c'i := (-4693/10000)) (r' := (261/10000)) (E := (1/10000)) (N := (22727/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (16341/10000)) (c'i := (-476/625)) (r' := (577/5000)) (E := (1/10000)) (N := (274/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3199/5000)) (c'i := (-12411/10000)) (r' := (43/100)) (E := (1/10000)) (N := (18029/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3861/1000)) (c'i := (28361/10000)) (r' := (13873/10000)) (E := (1/10000)) (N := (3491/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23953/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd322 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-259/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22373/10000)) (c'i := (1863/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (10023/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21367/10000)) (c'i := (-262/625)) (r' := (261/10000)) (E := (1/10000)) (N := (11341/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8299/5000)) (c'i := (-2717/5000)) (r' := (573/5000)) (E := (1/10000)) (N := (871/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2703/10000)) (c'i := (-5559/10000)) (r' := (207/500)) (E := (1/10000)) (N := (3493/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1483/500)) (c'i := (3097/2000)) (r' := (6841/10000)) (E := (1/10000)) (N := (3091/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16729/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd323 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-257/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22333/10000)) (c'i := (1897/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (10003/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21137/10000)) (c'i := (-2233/5000)) (r' := (13/500)) (E := (1/10000)) (N := (22653/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15383/10000)) (c'i := (-16/25)) (r' := (1133/10000)) (E := (1/10000)) (N := (5401/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1933/2500)) (c'i := (-721/1000)) (r' := (3909/10000)) (E := (1/10000)) (N := (8331/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-663/250)) (c'i := (2363/1000)) (r' := (1961/2000)) (E := (1/10000)) (N := (10573/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (444/125)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd319 : ∀ z : ℂ, |z.re - (221/256)| ≤ (1/256) → |z.im - (-129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd320 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd321 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd322 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd323 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd324 : ∀ z : ℂ, |z.re - (223/256)| ≤ (1/256) → |z.im - (-131/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (111/128)) (dy := (65/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd325 : ∀ z : ℂ, |z.re - (223/256)| ≤ (1/256) → |z.im - (-129/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (111/128)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd309 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-65/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd310 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd319 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd324 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd325 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd253 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-33/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd254 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd279 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd308 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd309 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd245 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-17/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd246 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd247 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd248 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd253 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd241 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd242 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd243 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd244 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd245 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd326 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-11/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (5/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd327 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-9/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (1/2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd239 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-5/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd240 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd241 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd326 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd327 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd235 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd236 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd237 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd238 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd239 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd329 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-62/25)) (c'i := (487/625)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5199/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd330 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-471/200)) (c'i := (5459/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (25957/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd333 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11697/5000)) (c'i := (1289/2500)) (r' := (207/2500)) (E := (1/10000)) (N := (9111/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4791/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd334 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22847/10000)) (c'i := (1533/2500)) (r' := (801/10000)) (E := (1/10000)) (N := (4403/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10569/5000)) (c'i := (-777/500)) (r' := (3859/10000)) (E := (1/10000)) (N := (2957/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-423/625)) (c'i := (-53217/10000)) (r' := (21761/10000)) (E := (1/10000)) (N := (6559/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10729/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd337 : ∀ z : ℂ, |z.re - (105/128)| ≤ (1/128) → |z.im - (-63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22993/10000)) (c'i := (881/2000)) (r' := (107/5000)) (E := (1/10000)) (N := (9567/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23411/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd338 : ∀ z : ℂ, |z.re - (105/128)| ≤ (1/128) → |z.im - (-61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11421/5000)) (c'i := (4661/10000)) (r' := (213/10000)) (E := (1/10000)) (N := (9487/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1457/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd339 : ∀ z : ℂ, |z.re - (107/128)| ≤ (1/128) → |z.im - (-63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4547/2000)) (c'i := (4251/10000)) (r' := (217/10000)) (E := (1/10000)) (N := (9701/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22581/10000)) (c'i := (-6849/10000)) (r' := (1011/10000)) (E := (1/10000)) (N := (2313/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18999/10000)) (c'i := (-18451/10000)) (r' := (61/125)) (E := (1/10000)) (N := (23597/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1578/625)) (c'i := (-5763/1000)) (r' := (28261/10000)) (E := (1/10000)) (N := (5297/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (62917/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd340 : ∀ z : ℂ, |z.re - (107/128)| ≤ (1/128) → |z.im - (-61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22583/10000)) (c'i := (282/625)) (r' := (27/1250)) (E := (1/10000)) (N := (9623/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21663/10000)) (c'i := (-7899/10000)) (r' := (501/5000)) (E := (1/10000)) (N := (2303/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13389/10000)) (c'i := (-21743/10000)) (r' := (591/1250)) (E := (1/10000)) (N := (23059/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-56649/10000)) (c'i := (-45743/10000)) (r' := (26409/10000)) (E := (1/10000)) (N := (5107/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (72811/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd336 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd337 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd338 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd339 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd340 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd341 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4499/2000)) (c'i := (199/400)) (r' := (53/1250)) (E := (1/10000)) (N := (118/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20827/10000)) (c'i := (-9903/10000)) (r' := (79/400)) (E := (1/10000)) (N := (23039/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6269/10000)) (c'i := (-2877/1000)) (r' := (9511/10000)) (E := (1/10000)) (N := (11531/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-106141/10000)) (c'i := (-2949/1250)) (r' := (521/80)) (E := (1/10000)) (N := (14723/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (108731/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd344 : ∀ z : ℂ, |z.re - (217/256)| ≤ (1/256) → |z.im - (-127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1411/625)) (c'i := (407/1000)) (r' := (11/1000)) (E := (1/10000)) (N := (4911/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (22011/10000)) (c'i := (-5897/10000)) (r' := (127/2500)) (E := (1/10000)) (N := (1147/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17671/10000)) (c'i := (-337/250)) (r' := (469/2000)) (E := (1/10000)) (N := (5697/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2849/2000)) (c'i := (-35161/10000)) (r' := (5493/5000)) (E := (1/10000)) (N := (11113/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2371/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd345 : ∀ z : ℂ, |z.re - (217/256)| ≤ (1/256) → |z.im - (-125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22499/10000)) (c'i := (2101/5000)) (r' := (11/1000)) (E := (1/10000)) (N := (9783/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4311/2000)) (c'i := (-1607/2500)) (r' := (507/10000)) (E := (1/10000)) (N := (22889/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1503/1000)) (c'i := (-15231/10000)) (r' := (231/1000)) (E := (1/10000)) (N := (11247/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6977/2500)) (c'i := (-4163/1250)) (r' := (652/625)) (E := (1/10000)) (N := (21399/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (43451/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd346 : ∀ z : ℂ, |z.re - (219/256)| ≤ (1/256) → |z.im - (-127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22443/10000)) (c'i := (499/1250)) (r' := (111/10000)) (E := (1/10000)) (N := (989/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (859/400)) (c'i := (-2719/5000)) (r' := (509/10000)) (E := (1/10000)) (N := (5699/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (793/500)) (c'i := (-2719/2500)) (r' := (457/2000)) (E := (1/10000)) (N := (22153/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-559/400)) (c'i := (-22019/10000)) (r' := (4661/5000)) (E := (1/10000)) (N := (19231/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28127/5000)) (c'i := (74023/10000)) (r' := (14343/2500)) (E := (1/10000)) (N := (326/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23243/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd347 : ∀ z : ℂ, |z.re - (219/256)| ≤ (1/256) → |z.im - (-125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11183/5000)) (c'i := (2063/5000)) (r' := (111/10000)) (E := (1/10000)) (N := (9851/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (21021/10000)) (c'i := (-747/1250)) (r' := (127/2500)) (E := (1/10000)) (N := (2843/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13317/10000)) (c'i := (-3161/2500)) (r' := (9/40)) (E := (1/10000)) (N := (10927/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-25553/10000)) (c'i := (-5299/2500)) (r' := (439/500)) (E := (1/10000)) (N := (4591/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (33199/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd343 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd344 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd345 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd346 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd347 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd348 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-279/125)) (c'i := (1091/2500)) (r' := (219/10000)) (E := (1/10000)) (N := (9759/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10307/5000)) (c'i := (-7001/10000)) (r' := (1003/10000)) (E := (1/10000)) (N := (22743/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2573/2500)) (c'i := (-1024/625)) (r' := (2237/5000)) (E := (1/10000)) (N := (21771/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-43551/10000)) (c'i := (-4249/2000)) (r' := (2417/1250)) (E := (1/10000)) (N := (19349/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6057/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd351 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11181/5000)) (c'i := (39/100)) (r' := (57/10000)) (E := (1/10000)) (N := (199/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4237/2000)) (c'i := (-2481/5000)) (r' := (261/10000)) (E := (1/10000)) (N := (227/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7559/5000)) (c'i := (-534/625)) (r' := (229/2000)) (E := (1/10000)) (N := (21759/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2349/2000)) (c'i := (-6677/5000)) (r' := (2057/5000)) (E := (1/10000)) (N := (8683/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-15669/5000)) (c'i := (43849/10000)) (r' := (2043/1250)) (E := (1/10000)) (N := (3557/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6737/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd352 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22323/10000)) (c'i := (248/625)) (r' := (57/10000)) (E := (1/10000)) (N := (9931/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20957/10000)) (c'i := (-1309/2500)) (r' := (261/10000)) (E := (1/10000)) (N := (22673/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6939/5000)) (c'i := (-4733/5000)) (r' := (1137/10000)) (E := (1/10000)) (N := (10801/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17001/10000)) (c'i := (-6897/5000)) (r' := (791/2000)) (E := (1/10000)) (N := (16799/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1089/625)) (c'i := (29691/5000)) (r' := (18903/10000)) (E := (1/10000)) (N := (10947/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12377/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd353 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11147/5000)) (c'i := (3861/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (624/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1307/625)) (c'i := (-947/2000)) (r' := (13/500)) (E := (1/10000)) (N := (11313/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (14189/10000)) (c'i := (-1831/2500)) (r' := (281/2500)) (E := (1/10000)) (N := (10721/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12531/10000)) (c'i := (-519/625)) (r' := (3721/10000)) (E := (1/10000)) (N := (998/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18493/10000)) (c'i := (33291/10000)) (r' := (6293/5000)) (E := (1/10000)) (N := (15033/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (19041/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd354 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4451/2000)) (c'i := (3929/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (2491/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4137/2000)) (c'i := (-313/625)) (r' := (13/500)) (E := (1/10000)) (N := (113/50)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12979/10000)) (c'i := (-4119/5000)) (r' := (279/2500)) (E := (1/10000)) (N := (21283/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-17241/10000)) (c'i := (-1113/1250)) (r' := (3561/10000)) (E := (1/10000)) (N := (15373/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5503/10000)) (c'i := (43183/10000)) (r' := (3021/2000)) (E := (1/10000)) (N := (3881/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10883/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd350 : ∀ z : ℂ, |z.re - (221/256)| ≤ (1/256) → |z.im - (-127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd351 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd352 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd353 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd354 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd356 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5571/2500)) (c'i := (807/2000)) (r' := (7/1250)) (E := (1/10000)) (N := (9911/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2073/1000)) (c'i := (-5503/10000)) (r' := (16/625)) (E := (1/10000)) (N := (22647/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2529/2000)) (c'i := (-2067/2000)) (r' := (1107/10000)) (E := (1/10000)) (N := (21449/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2749/1250)) (c'i := (-13657/10000)) (r' := (234/625)) (E := (1/10000)) (N := (4083/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2413/10000)) (c'i := (72549/10000)) (r' := (20809/10000)) (E := (1/10000)) (N := (1618/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (72589/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd357 : ∀ z : ℂ, |z.re - (441/512)| ≤ (1/512) → |z.im - (-249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11123/5000)) (c'i := (2051/5000)) (r' := (7/1250)) (E := (1/10000)) (N := (2473/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10253/5000)) (c'i := (-5771/10000)) (r' := (51/2000)) (E := (1/10000)) (N := (11311/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (11419/10000)) (c'i := (-2797/2500)) (r' := (137/1250)) (E := (1/10000)) (N := (21303/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-13389/5000)) (c'i := (-13071/10000)) (r' := (363/1000)) (E := (1/10000)) (N := (15987/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29797/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd358 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22217/10000)) (c'i := (3997/10000)) (r' := (57/10000)) (E := (1/10000)) (N := (1989/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10231/5000)) (c'i := (-66/125)) (r' := (259/10000)) (E := (1/10000)) (N := (11287/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5891/5000)) (c'i := (-1141/1250)) (r' := (69/625)) (E := (1/10000)) (N := (21133/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-87/40)) (c'i := (-9029/10000)) (r' := (1709/5000)) (E := (1/10000)) (N := (2981/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5927/5000)) (c'i := (12939/2500)) (r' := (8643/5000)) (E := (1/10000)) (N := (471/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6637/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd359 : ∀ z : ℂ, |z.re - (443/512)| ≤ (1/512) → |z.im - (-249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22179/10000)) (c'i := (254/625)) (r' := (7/1250)) (E := (1/10000)) (N := (4963/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20239/10000)) (c'i := (-5547/10000)) (r' := (51/2000)) (E := (1/10000)) (N := (22549/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2117/2000)) (c'i := (-9973/10000)) (r' := (1079/10000)) (E := (1/10000)) (N := (10493/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-13021/5000)) (c'i := (-8633/10000)) (r' := (163/500)) (E := (1/10000)) (N := (909/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5487/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd355 : ∀ z : ℂ, |z.re - (221/256)| ≤ (1/256) → |z.im - (-125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd356 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd357 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd358 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd359 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd362 : ∀ z : ℂ, |z.re - (889/1024)| ≤ (1/1024) → |z.im - (-511/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (111/128)) (dy := (255/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd363 : ∀ z : ℂ, |z.re - (889/1024)| ≤ (1/1024) → |z.im - (-509/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11117/5000)) (c'i := (3849/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (2501/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10327/5000)) (c'i := (-1159/2500)) (r' := (133/10000)) (E := (1/10000)) (N := (4513/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1321/1000)) (c'i := (-667/1000)) (r' := (567/10000)) (E := (1/10000)) (N := (1323/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7149/5000)) (c'i := (-2571/5000)) (r' := (857/5000)) (E := (1/10000)) (N := (14799/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9501/10000)) (c'i := (1699/625)) (r' := (551/1000)) (E := (1/10000)) (N := (3039/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7199/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd364 : ∀ z : ℂ, |z.re - (891/1024)| ≤ (1/1024) → |z.im - (-511/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (445/512)) (dy := (255/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd365 : ∀ z : ℂ, |z.re - (891/1024)| ≤ (1/1024) → |z.im - (-509/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (445/512)) (dy := (127/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd361 : ∀ z : ℂ, |z.re - (445/512)| ≤ (1/512) → |z.im - (-255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd362 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd363 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd364 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd365 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd367 : ∀ z : ℂ, |z.re - (889/1024)| ≤ (1/1024) → |z.im - (-507/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11107/5000)) (c'i := (3883/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (1999/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10269/5000)) (c'i := (-4771/10000)) (r' := (133/10000)) (E := (1/10000)) (N := (22551/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2521/2000)) (c'i := (-7117/10000)) (r' := (113/2000)) (E := (1/10000)) (N := (4217/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16477/10000)) (c'i := (-2731/5000)) (r' := (1671/10000)) (E := (1/10000)) (N := (3619/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1567/5000)) (c'i := (30479/10000)) (r' := (761/1250)) (E := (1/10000)) (N := (17359/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30639/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd368 : ∀ z : ℂ, |z.re - (889/1024)| ≤ (1/1024) → |z.im - (-505/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4439/2000)) (c'i := (3917/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (1997/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5107/2500)) (c'i := (-1227/2500)) (r' := (33/2500)) (E := (1/10000)) (N := (22539/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12021/10000)) (c'i := (-1893/2500)) (r' := (279/5000)) (E := (1/10000)) (N := (2101/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18583/10000)) (c'i := (-229/400)) (r' := (81/500)) (E := (1/10000)) (N := (888/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (791/2000)) (c'i := (16879/5000)) (r' := (6571/10000)) (E := (1/10000)) (N := (3889/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (8497/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd369 : ∀ z : ℂ, |z.re - (891/1024)| ≤ (1/1024) → |z.im - (-507/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1109/500)) (c'i := (483/1250)) (r' := (29/10000)) (E := (1/10000)) (N := (2503/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10201/5000)) (c'i := (-4661/10000)) (r' := (33/2500)) (E := (1/10000)) (N := (4503/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1519/1250)) (c'i := (-6539/10000)) (r' := (139/2500)) (E := (1/10000)) (N := (1308/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16809/10000)) (c'i := (-853/2500)) (r' := (1569/10000)) (E := (1/10000)) (N := (69/50)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21/1000)) (c'i := (479/200)) (r' := (1409/2500)) (E := (1/10000)) (N := (1072/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5291/625)) (c'i := (5737/5000)) (r' := (15103/5000)) (E := (1/10000)) (N := (23951/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (85429/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd370 : ∀ z : ℂ, |z.re - (891/1024)| ≤ (1/1024) → |z.im - (-505/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22161/10000)) (c'i := (1949/5000)) (r' := (29/10000)) (E := (1/10000)) (N := (5001/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5073/2500)) (c'i := (-4797/10000)) (r' := (33/2500)) (E := (1/10000)) (N := (11251/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (463/400)) (c'i := (-1747/2500)) (r' := (277/5000)) (E := (1/10000)) (N := (5213/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3757/2000)) (c'i := (-3697/10000)) (r' := (383/2500)) (E := (1/10000)) (N := (13521/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6621/10000)) (c'i := (2637/1000)) (r' := (6109/10000)) (E := (1/10000)) (N := (9573/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-46227/5000)) (c'i := (47399/10000)) (r' := (3699/1000)) (E := (1/10000)) (N := (27189/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (12987/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd366 : ∀ z : ℂ, |z.re - (445/512)| ≤ (1/512) → |z.im - (-253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd367 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd368 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd369 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd370 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd371 : ∀ z : ℂ, |z.re - (447/512)| ≤ (1/512) → |z.im - (-255/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (223/256)) (dy := (127/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd372 : ∀ z : ℂ, |z.re - (447/512)| ≤ (1/512) → |z.im - (-253/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (223/256)) (dy := (63/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd360 : ∀ z : ℂ, |z.re - (223/256)| ≤ (1/256) → |z.im - (-127/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd361 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd366 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd371 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd372 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd374 : ∀ z : ℂ, |z.re - (445/512)| ≤ (1/512) → |z.im - (-251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22149/10000)) (c'i := (1979/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (9979/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (20191/10000)) (c'i := (-5053/10000)) (r' := (259/10000)) (E := (1/10000)) (N := (9/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5457/5000)) (c'i := (-317/400)) (r' := (1087/10000)) (E := (1/10000)) (N := (10407/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-21669/10000)) (c'i := (-4819/10000)) (r' := (611/2000)) (E := (1/10000)) (N := (843/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4333/2500)) (c'i := (6673/2000)) (r' := (14513/10000)) (E := (1/10000)) (N := (22199/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (18799/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd375 : ∀ z : ℂ, |z.re - (445/512)| ≤ (1/512) → |z.im - (-249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22111/10000)) (c'i := (2013/5000)) (r' := (57/10000)) (E := (1/10000)) (N := (249/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19969/10000)) (c'i := (-1331/2500)) (r' := (129/5000)) (E := (1/10000)) (N := (899/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4871/5000)) (c'i := (-8783/10000)) (r' := (269/2500)) (E := (1/10000)) (N := (20667/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-25523/10000)) (c'i := (-4633/10000)) (r' := (2943/10000)) (E := (1/10000)) (N := (13117/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2231/625)) (c'i := (3613/1000)) (r' := (16153/10000)) (E := (1/10000)) (N := (25941/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (50789/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd377 : ∀ z : ℂ, |z.re - (893/1024)| ≤ (1/1024) → |z.im - (-503/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5527/2500)) (c'i := (3913/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (10009/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4009/2000)) (c'i := (-2411/5000)) (r' := (33/2500)) (E := (1/10000)) (N := (5613/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2111/2000)) (c'i := (-6851/10000)) (r' := (137/2500)) (E := (1/10000)) (N := (20617/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-20853/10000)) (c'i := (-991/5000)) (r' := (353/2500)) (E := (1/10000)) (N := (1573/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (987/625)) (c'i := (10373/5000)) (r' := (6123/10000)) (E := (1/10000)) (N := (5237/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-45401/10000)) (c'i := (19501/2500)) (r' := (7143/2000)) (E := (1/10000)) (N := (26073/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (45127/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd378 : ∀ z : ℂ, |z.re - (893/1024)| ≤ (1/1024) → |z.im - (-501/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22089/10000)) (c'i := (3947/10000)) (r' := (29/10000)) (E := (1/10000)) (N := (1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3987/2000)) (c'i := (-4957/10000)) (r' := (33/2500)) (E := (1/10000)) (N := (22439/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9983/10000)) (c'i := (-1821/2500)) (r' := (273/5000)) (E := (1/10000)) (N := (20543/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-283/125)) (c'i := (-2063/10000)) (r' := (691/5000)) (E := (1/10000)) (N := (6179/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (23531/10000)) (c'i := (21821/10000)) (r' := (6483/10000)) (E := (1/10000)) (N := (11367/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32091/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd379 : ∀ z : ℂ, |z.re - (895/1024)| ≤ (1/1024) → |z.im - (-503/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (447/512)) (dy := (251/512)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd380 : ∀ z : ℂ, |z.re - (895/1024)| ≤ (1/1024) → |z.im - (-501/1024)| ≤ (1/1024) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (447/512)) (dy := (125/256)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd376 : ∀ z : ℂ, |z.re - (447/512)| ≤ (1/512) → |z.im - (-251/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd377 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd378 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd379 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd380 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd381 : ∀ z : ℂ, |z.re - (447/512)| ≤ (1/512) → |z.im - (-249/512)| ≤ (1/512) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22043/10000)) (c'i := (997/2500)) (r' := (57/10000)) (E := (1/10000)) (N := (4997/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19699/10000)) (c'i := (-5101/10000)) (r' := (257/10000)) (E := (1/10000)) (N := (22401/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8903/10000)) (c'i := (-7617/10000)) (r' := (211/2000)) (E := (1/10000)) (N := (20349/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3147/1250)) (c'i := (-1083/10000)) (r' := (647/2500)) (E := (1/10000)) (N := (11717/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17983/5000)) (c'i := (17933/10000)) (r' := (13729/10000)) (E := (1/10000)) (N := (63/25)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (10047/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd373 : ∀ z : ℂ, |z.re - (223/256)| ≤ (1/256) → |z.im - (-125/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd374 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd375 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd376 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd381 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd349 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd350 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd355 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd360 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd373 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd383 : ∀ z : ℂ, |z.re - (221/256)| ≤ (1/256) → |z.im - (-123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5539/2500)) (c'i := (523/1250)) (r' := (111/10000)) (E := (1/10000)) (N := (247/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10019/5000)) (c'i := (-303/500)) (r' := (63/1250)) (E := (1/10000)) (N := (5637/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (459/500)) (c'i := (-5903/5000)) (r' := (2139/10000)) (E := (1/10000)) (N := (4187/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-32811/10000)) (c'i := (-2299/2500)) (r' := (429/625)) (E := (1/10000)) (N := (3739/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1363/400)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd384 : ∀ z : ℂ, |z.re - (221/256)| ≤ (1/256) → |z.im - (-121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22081/10000)) (c'i := (4319/10000)) (r' := (111/10000)) (E := (1/10000)) (N := (9843/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2449/1250)) (c'i := (-3297/5000)) (r' := (503/10000)) (E := (1/10000)) (N := (9/4)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (6737/10000)) (c'i := (-6679/5000)) (r' := (2109/10000)) (E := (1/10000)) (N := (1292/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8121/2000)) (c'i := (-5519/10000)) (r' := (1691/2500)) (E := (1/10000)) (N := (14961/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (20489/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd385 : ∀ z : ℂ, |z.re - (223/256)| ≤ (1/256) → |z.im - (-123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1101/500)) (c'i := (4109/10000)) (r' := (7/625)) (E := (1/10000)) (N := (9949/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (39/20)) (c'i := (-351/625)) (r' := (101/2000)) (E := (1/10000)) (N := (22401/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (7571/10000)) (c'i := (-4711/5000)) (r' := (2079/10000)) (E := (1/10000)) (N := (20293/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6089/2000)) (c'i := (-1787/10000)) (r' := (1093/2000)) (E := (1/10000)) (N := (12087/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (30497/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd386 : ∀ z : ℂ, |z.re - (223/256)| ≤ (1/256) → |z.im - (-121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10973/5000)) (c'i := (849/2000)) (r' := (111/10000)) (E := (1/10000)) (N := (9911/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19061/10000)) (c'i := (-769/1250)) (r' := (499/10000)) (E := (1/10000)) (N := (22353/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5247/10000)) (c'i := (-10973/10000)) (r' := (2027/10000)) (E := (1/10000)) (N := (2003/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9147/2500)) (c'i := (193/2000)) (r' := (5349/10000)) (E := (1/10000)) (N := (12163/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (183/50)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd382 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd383 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd384 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd385 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd386 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd342 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd343 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd348 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd349 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd382 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd388 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22173/10000)) (c'i := (463/1000)) (r' := (217/10000)) (E := (1/10000)) (N := (2421/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (19721/10000)) (c'i := (-2013/2500)) (r' := (99/1000)) (E := (1/10000)) (N := (5663/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1277/2500)) (c'i := (-19279/10000)) (r' := (2161/5000)) (E := (1/10000)) (N := (10651/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-61859/10000)) (c'i := (-1443/2000)) (r' := (19129/10000)) (E := (1/10000)) (N := (3989/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31139/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd389 : ∀ z : ℂ, |z.re - (109/128)| ≤ (1/128) → |z.im - (-57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-22031/10000)) (c'i := (306/625)) (r' := (43/2000)) (E := (1/10000)) (N := (961/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18839/10000)) (c'i := (-9093/10000)) (r' := (489/5000)) (E := (1/10000)) (N := (22569/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-77/10000)) (c'i := (-21781/10000)) (r' := (4193/10000)) (E := (1/10000)) (N := (20919/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-74741/10000)) (c'i := (2563/2000)) (r' := (10023/5000)) (E := (1/10000)) (N := (10891/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (75831/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd390 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1369/625)) (c'i := (2243/5000)) (r' := (11/500)) (E := (1/10000)) (N := (9821/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (9333/5000)) (c'i := (-1793/2500)) (r' := (991/10000)) (E := (1/10000)) (N := (22359/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1199/5000)) (c'i := (-2859/2000)) (r' := (4067/10000)) (E := (1/10000)) (N := (19997/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1179/250)) (c'i := (703/1250)) (r' := (13459/10000)) (E := (1/10000)) (N := (2899/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23747/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd391 : ∀ z : ℂ, |z.re - (111/128)| ≤ (1/128) → |z.im - (-57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21763/10000)) (c'i := (4757/10000)) (r' := (109/5000)) (E := (1/10000)) (N := (9749/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (89/50)) (c'i := (-329/400)) (r' := (979/10000)) (E := (1/10000)) (N := (22277/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2381/10000)) (c'i := (-16801/10000)) (r' := (3941/10000)) (E := (1/10000)) (N := (19609/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-687/125)) (c'i := (20481/10000)) (r' := (2989/2000)) (E := (1/10000)) (N := (16969/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (14663/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd387 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd388 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd389 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd390 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd391 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd335 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd336 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd341 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd342 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd387 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd393 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11111/5000)) (c'i := (5493/10000)) (r' := (209/5000)) (E := (1/10000)) (N := (4647/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2383/1250)) (c'i := (-11933/10000)) (r' := (387/2000)) (E := (1/10000)) (N := (22891/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1299/2500)) (c'i := (-16509/5000)) (r' := (9089/10000)) (E := (1/10000)) (N := (22491/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2089/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd394 : ∀ z : ℂ, |z.re - (53/64)| ≤ (1/64) → |z.im - (-25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-1373/625)) (c'i := (601/1000)) (r' := (103/2500)) (E := (1/10000)) (N := (9157/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17347/10000)) (c'i := (-6963/5000)) (r' := (1897/10000)) (E := (1/10000)) (N := (2847/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8301/5000)) (c'i := (-7167/2000)) (r' := (881/1000)) (E := (1/10000)) (N := (11123/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (39493/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd395 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4339/2000)) (c'i := (5229/10000)) (r' := (43/1000)) (E := (1/10000)) (N := (4787/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (17033/10000)) (c'i := (-10209/10000)) (r' := (1941/10000)) (E := (1/10000)) (N := (22317/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-871/1000)) (c'i := (-11149/5000)) (r' := (506/625)) (E := (1/10000)) (N := (19859/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-34717/5000)) (c'i := (51323/10000)) (r' := (45363/10000)) (E := (1/10000)) (N := (23939/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (86343/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd396 : ∀ z : ℂ, |z.re - (55/64)| ≤ (1/64) → |z.im - (-25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21441/10000)) (c'i := (2883/5000)) (r' := (53/1250)) (E := (1/10000)) (N := (118/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15347/10000)) (c'i := (-6123/5000)) (r' := (119/625)) (E := (1/10000)) (N := (22203/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18743/10000)) (c'i := (-6277/2500)) (r' := (7849/10000)) (E := (1/10000)) (N := (3927/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (7833/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd392 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd393 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd394 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd395 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd396 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd332 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd333 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd334 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd335 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd392 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd398 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-11189/5000)) (c'i := (7109/10000)) (r' := (777/10000)) (E := (1/10000)) (N := (1067/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4431/2500)) (c'i := (-19337/10000)) (r' := (743/2000)) (E := (1/10000)) (N := (23481/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-16639/5000)) (c'i := (-28033/5000)) (r' := (5223/2500)) (E := (1/10000)) (N := (26231/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (32599/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd399 : ∀ z : ℂ, |z.re - (25/32)| ≤ (1/32) → |z.im - (-9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5497/2500)) (c'i := (1617/2000)) (r' := (189/2500)) (E := (1/10000)) (N := (519/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1451/1000)) (c'i := (-923/400)) (r' := (721/2000)) (E := (1/10000)) (N := (5857/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (27257/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd400 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10681/5000)) (c'i := (6679/10000)) (r' := (207/2500)) (E := (1/10000)) (N := (9111/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13873/10000)) (c'i := (-3211/2000)) (r' := (189/500)) (E := (1/10000)) (N := (11191/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3383/1000)) (c'i := (-16033/5000)) (r' := (17489/10000)) (E := (1/10000)) (N := (21219/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (11653/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd401 : ∀ z : ℂ, |z.re - (27/32)| ≤ (1/32) → |z.im - (-9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5243/2500)) (c'i := (3867/5000)) (r' := (101/1250)) (E := (1/10000)) (N := (4447/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10701/10000)) (c'i := (-19959/10000)) (r' := (3683/10000)) (E := (1/10000)) (N := (22353/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-11137/2000)) (c'i := (-7559/2500)) (r' := (9029/5000)) (E := (1/10000)) (N := (22647/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15841/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd397 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd398 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd399 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd400 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd401 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd405 : ∀ z : ℂ, |z.re - (113/128)| ≤ (1/128) → |z.im - (-63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (7/8)) (dy := (31/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd407 : ∀ z : ℂ, |z.re - (225/256)| ≤ (1/256) → |z.im - (-123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5471/2500)) (c'i := (2017/5000)) (r' := (113/10000)) (E := (1/10000)) (N := (10017/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4741/2500)) (c'i := (-647/1250)) (r' := (253/5000)) (E := (1/10000)) (N := (22253/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (374/625)) (c'i := (-447/625)) (r' := (2019/10000)) (E := (1/10000)) (N := (9829/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-14417/5000)) (c'i := (49/125)) (r' := (4179/10000)) (E := (1/10000)) (N := (4663/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (29099/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd408 : ∀ z : ℂ, |z.re - (225/256)| ≤ (1/256) → |z.im - (-121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21809/10000)) (c'i := (1043/2500)) (r' := (7/625)) (E := (1/10000)) (N := (499/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (18523/10000)) (c'i := (-5717/10000)) (r' := (501/10000)) (E := (1/10000)) (N := (4441/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1871/5000)) (c'i := (-8699/10000)) (r' := (1971/10000)) (E := (1/10000)) (N := (9693/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-33467/10000)) (c'i := (597/1000)) (r' := (4127/10000)) (E := (1/10000)) (N := (947/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6799/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd409 : ∀ z : ℂ, |z.re - (227/256)| ≤ (1/256) → |z.im - (-123/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (113/128)) (dy := (61/128)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd410 : ∀ z : ℂ, |z.re - (227/256)| ≤ (1/256) → |z.im - (-121/256)| ≤ (1/256) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21671/10000)) (c'i := (2049/5000)) (r' := (113/10000)) (E := (1/10000)) (N := (10049/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1124/625)) (c'i := (-2641/5000)) (r' := (251/5000)) (E := (1/10000)) (N := (2757/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (563/2500)) (c'i := (-3259/5000)) (r' := (1911/10000)) (E := (1/10000)) (N := (2343/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-31041/10000)) (c'i := (1193/1250)) (r' := (1503/5000)) (E := (1/10000)) (N := (6897/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1299/400)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd406 : ∀ z : ℂ, |z.re - (113/128)| ≤ (1/128) → |z.im - (-61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd407 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd408 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd409 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd410 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd411 : ∀ z : ℂ, |z.re - (115/128)| ≤ (1/128) → |z.im - (-63/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (57/64)) (dy := (31/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd412 : ∀ z : ℂ, |z.re - (115/128)| ≤ (1/128) → |z.im - (-61/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (57/64)) (dy := (15/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd404 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd405 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd406 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd411 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd412 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd414 : ∀ z : ℂ, |z.re - (113/128)| ≤ (1/128) → |z.im - (-59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21631/10000)) (c'i := (2171/5000)) (r' := (223/10000)) (E := (1/10000)) (N := (249/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3521/2000)) (c'i := (-394/625)) (r' := (991/10000)) (E := (1/10000)) (N := (22063/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7/250)) (c'i := (-2429/2500)) (r' := (381/1000)) (E := (1/10000)) (N := (187/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9183/2500)) (c'i := (814/625)) (r' := (8869/10000)) (E := (1/10000)) (N := (9721/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9743/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd415 : ∀ z : ℂ, |z.re - (113/128)| ≤ (1/128) → |z.im - (-57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21489/10000)) (c'i := (4617/10000)) (r' := (111/5000)) (E := (1/10000)) (N := (618/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8373/5000)) (c'i := (-7363/10000)) (r' := (983/10000)) (E := (1/10000)) (N := (1099/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4679/10000)) (c'i := (-609/500)) (r' := (1849/5000)) (E := (1/10000)) (N := (9147/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-19973/5000)) (c'i := (11939/5000)) (r' := (1103/1000)) (E := (1/10000)) (N := (1631/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23269/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd416 : ∀ z : ℂ, |z.re - (115/128)| ≤ (1/128) → |z.im - (-59/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21353/10000)) (c'i := (2099/5000)) (r' := (113/5000)) (E := (1/10000)) (N := (5049/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (16533/10000)) (c'i := (-681/1250)) (r' := (991/10000)) (E := (1/10000)) (N := (10881/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1467/5000)) (c'i := (-2767/5000)) (r' := (1777/5000)) (E := (1/10000)) (N := (1088/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-14751/5000)) (c'i := (15727/10000)) (r' := (5723/10000)) (E := (1/10000)) (N := (783/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (4179/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd417 : ∀ z : ℂ, |z.re - (115/128)| ≤ (1/128) → |z.im - (-57/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21211/10000)) (c'i := (2239/5000)) (r' := (9/400)) (E := (1/10000)) (N := (2507/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3137/2000)) (c'i := (-6517/10000)) (r' := (983/10000)) (E := (1/10000)) (N := (21679/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1389/2000)) (c'i := (-1991/2500)) (r' := (3441/10000)) (E := (1/10000)) (N := (8493/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-28819/10000)) (c'i := (11771/5000)) (r' := (4233/5000)) (E := (1/10000)) (N := (10567/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9303/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd413 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd414 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd415 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd416 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd417 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd418 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-31/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (15/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd419 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-29/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (29/32)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd403 : ∀ z : ℂ, |z.re - (29/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd404 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd413 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd418 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd419 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd422 : ∀ z : ℂ, |z.re - (113/128)| ≤ (1/128) → |z.im - (-55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21353/10000)) (c'i := (4893/10000)) (r' := (11/500)) (E := (1/10000)) (N := (9819/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15901/10000)) (c'i := (-526/625)) (r' := (971/10000)) (E := (1/10000)) (N := (21907/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9099/10000)) (c'i := (-2857/2000)) (r' := (3593/10000)) (E := (1/10000)) (N := (17991/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-39427/10000)) (c'i := (9619/2500)) (r' := (13477/10000)) (E := (1/10000)) (N := (16937/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (55089/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd423 : ∀ z : ℂ, |z.re - (113/128)| ≤ (1/128) → |z.im - (-53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-21221/10000)) (c'i := (5169/10000)) (r' := (219/10000)) (E := (1/10000)) (N := (9751/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (15061/10000)) (c'i := (-4729/5000)) (r' := (241/2500)) (E := (1/10000)) (N := (10921/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6781/5000)) (c'i := (-16009/10000)) (r' := (3527/10000)) (E := (1/10000)) (N := (3557/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-4317/1250)) (c'i := (55903/10000)) (r' := (8031/5000)) (E := (1/10000)) (N := (10491/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (6571/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd424 : ∀ z : ℂ, |z.re - (115/128)| ≤ (1/128) → |z.im - (-55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10537/5000)) (c'i := (4759/10000)) (r' := (223/10000)) (E := (1/10000)) (N := (249/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (14847/10000)) (c'i := (-3789/5000)) (r' := (971/10000)) (E := (1/10000)) (N := (4321/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10999/10000)) (c'i := (-5011/5000)) (r' := (417/1250)) (E := (1/10000)) (N := (1667/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-12623/5000)) (c'i := (17263/5000)) (r' := (5527/5000)) (E := (1/10000)) (N := (14881/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (42771/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd425 : ∀ z : ℂ, |z.re - (115/128)| ≤ (1/128) → |z.im - (-53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20943/10000)) (c'i := (63/125)) (r' := (111/5000)) (E := (1/10000)) (N := (9893/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (14021/10000)) (c'i := (-8631/10000)) (r' := (241/2500)) (E := (1/10000)) (N := (21541/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-15091/10000)) (c'i := (-11723/10000)) (r' := (409/1250)) (E := (1/10000)) (N := (3293/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-18269/10000)) (c'i := (23931/5000)) (r' := (13591/10000)) (E := (1/10000)) (N := (1911/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (5123/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd421 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd422 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd423 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd424 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd425 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd426 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10447/5000)) (c'i := (2761/5000)) (r' := (437/10000)) (E := (1/10000)) (N := (4863/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (13307/10000)) (c'i := (-2119/2000)) (r' := (1911/10000)) (E := (1/10000)) (N := (5403/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-10409/5000)) (c'i := (-7859/5000)) (r' := (11/16)) (E := (1/10000)) (N := (1701/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-8667/10000)) (c'i := (77923/10000)) (r' := (40637/10000)) (E := (1/10000)) (N := (13043/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (78403/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd428 : ∀ z : ℂ, |z.re - (117/128)| ≤ (1/128) → |z.im - (-55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20791/10000)) (c'i := (37/80)) (r' := (113/5000)) (E := (1/10000)) (N := (10101/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3447/2500)) (c'i := (-422/625)) (r' := (97/1000)) (E := (1/10000)) (N := (213/100)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-803/625)) (c'i := (-6139/10000)) (r' := (3077/10000)) (E := (1/10000)) (N := (15353/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-7281/5000)) (c'i := (5651/2000)) (r' := (9721/10000)) (E := (1/10000)) (N := (178/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-85929/10000)) (c'i := (-6981/1000)) (r' := (71323/10000)) (E := (1/10000)) (N := (31787/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13839/1250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd429 : ∀ z : ℂ, |z.re - (117/128)| ≤ (1/128) → |z.im - (-53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20659/10000)) (c'i := (491/1000)) (r' := (9/400)) (E := (1/10000)) (N := (2007/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (12969/10000)) (c'i := (-7807/10000)) (r' := (963/10000)) (E := (1/10000)) (N := (4247/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-663/400)) (c'i := (-777/1000)) (r' := (3013/10000)) (E := (1/10000)) (N := (7569/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-733/1250)) (c'i := (19119/5000)) (r' := (747/625)) (E := (1/10000)) (N := (9153/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9671/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd430 : ∀ z : ℂ, |z.re - (119/128)| ≤ (1/128) → |z.im - (-55/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (59/64)) (dy := (27/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd431 : ∀ z : ℂ, |z.re - (119/128)| ≤ (1/128) → |z.im - (-53/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (59/64)) (dy := (13/32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd427 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-27/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd428 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd429 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd430 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd431 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd433 : ∀ z : ℂ, |z.re - (117/128)| ≤ (1/128) → |z.im - (-51/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-5133/2500)) (c'i := (1299/2500)) (r' := (223/10000)) (E := (1/10000)) (N := (2493/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (3039/2500)) (c'i := (-8857/10000)) (r' := (119/1250)) (E := (1/10000)) (N := (1059/500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-1273/625)) (c'i := (-9053/10000)) (r' := (2959/10000)) (E := (1/10000)) (N := (15041/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (599/1000)) (c'i := (24679/5000)) (r' := (7041/5000)) (E := (1/10000)) (N := (2229/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1243/250)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd434 : ∀ z : ℂ, |z.re - (117/128)| ≤ (1/128) → |z.im - (-49/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-2041/1000)) (c'i := (2741/5000)) (r' := (111/5000)) (E := (1/10000)) (N := (991/1000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1419/1250)) (c'i := (-4949/5000)) (r' := (473/5000)) (E := (1/10000)) (N := (10567/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-2421/1000)) (c'i := (-1249/1250)) (r' := (184/625)) (E := (1/10000)) (N := (7531/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (2619/1000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd435 : ∀ z : ℂ, |z.re - (119/128)| ≤ (1/128) → |z.im - (-51/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (59/64)) (dy := (25/64)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd436 : ∀ z : ℂ, |z.re - (119/128)| ≤ (1/128) → |z.im - (-49/128)| ≤ (1/128) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10061/5000)) (c'i := (2681/5000)) (r' := (9/400)) (E := (1/10000)) (N := (2011/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (5157/5000)) (c'i := (-9099/10000)) (r' := (189/2000)) (E := (1/10000)) (N := (833/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-24941/10000)) (c'i := (-6289/10000)) (r' := (2693/10000)) (E := (1/10000)) (N := (6877/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (619/200)) (c'i := (43851/10000)) (r' := (2919/2000)) (E := (1/10000)) (N := (12861/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (53673/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd432 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-25/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd433 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd434 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd435 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd436 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd420 : ∀ z : ℂ, |z.re - (29/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd421 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd426 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd427 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd432 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd437 : ∀ z : ℂ, |z.re - (31/32)| ≤ (1/32) → |z.im - (-15/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (7/16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd438 : ∀ z : ℂ, |z.re - (31/32)| ≤ (1/32) → |z.im - (-13/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := (15/16)) (dy := (3/8)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)
  have nd402 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-7/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd403 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd420 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd437 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd438 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd441 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-23/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20659/10000)) (c'i := (6079/10000)) (r' := (431/10000)) (E := (1/10000)) (N := (2401/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2921/2500)) (c'i := (-12637/10000)) (r' := (939/5000)) (E := (1/10000)) (N := (4307/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-14809/5000)) (c'i := (-341/200)) (r' := (273/400)) (E := (1/10000)) (N := (17211/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (17087/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd442 : ∀ z : ℂ, |z.re - (57/64)| ≤ (1/64) → |z.im - (-21/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-4089/2000)) (c'i := (1327/2000)) (r' := (427/10000)) (E := (1/10000)) (N := (2373/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (10097/10000)) (c'i := (-14651/10000)) (r' := (1857/10000)) (E := (1/10000)) (N := (4299/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-3857/1000)) (c'i := (-8553/5000)) (r' := (3481/5000)) (E := (1/10000)) (N := (8897/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (42193/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd443 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-23/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-20093/10000)) (c'i := (2927/5000)) (r' := (111/2500)) (E := (1/10000)) (N := (1979/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (4823/5000)) (c'i := (-2209/2000)) (r' := (941/5000)) (E := (1/10000)) (N := (20929/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-6039/2000)) (c'i := (-2207/2500)) (r' := (5881/10000)) (E := (1/10000)) (N := (2933/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (31459/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd444 : ∀ z : ℂ, |z.re - (59/64)| ≤ (1/64) → |z.im - (-21/64)| ≤ (1/64) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9939/5000)) (c'i := (643/1000)) (r' := (11/250)) (E := (1/10000)) (N := (4893/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (8079/10000)) (c'i := (-13083/10000)) (r' := (1861/10000)) (E := (1/10000)) (N := (20893/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-37889/10000)) (c'i := (-433/500)) (r' := (6077/10000)) (E := (1/10000)) (N := (15377/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (19433/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd440 : ∀ z : ℂ, |z.re - (29/32)| ≤ (1/32) → |z.im - (-11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd441 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd442 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd443 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd444 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd445 : ∀ z : ℂ, |z.re - (29/32)| ≤ (1/32) → |z.im - (-9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9939/5000)) (c'i := (3691/5000)) (r' := (861/10000)) (E := (1/10000)) (N := (9489/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (1691/2500)) (c'i := (-4217/2500)) (r' := (3731/10000)) (E := (1/10000)) (N := (4241/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-25589/5000)) (c'i := (-10339/10000)) (r' := (1497/1000)) (E := (1/10000)) (N := (9087/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (52211/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd446 : ∀ z : ℂ, |z.re - (31/32)| ≤ (1/32) → |z.im - (-11/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-19097/10000)) (c'i := (291/500)) (r' := (931/10000)) (E := (1/10000)) (N := (257/250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (2891/5000)) (c'i := (-9749/10000)) (r' := (3809/10000)) (E := (1/10000)) (N := (3993/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-33461/10000)) (c'i := (603/5000)) (r' := (10097/10000)) (E := (1/10000)) (N := (2267/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (16741/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd447 : ∀ z : ℂ, |z.re - (31/32)| ≤ (1/32) → |z.im - (-9/32)| ≤ (1/32) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9353/5000)) (c'i := (7031/10000)) (r' := (457/5000)) (E := (1/10000)) (N := (1261/1250)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (687/2500)) (c'i := (-864/625)) (r' := (1871/5000)) (E := (1/10000)) (N := (1249/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9131/2000)) (c'i := (2441/5000)) (r' := (5981/5000)) (E := (1/10000)) (N := (2819/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9183/2000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd439 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-5/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd440 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd445 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd446 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd447 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd331 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd332 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd397 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd402 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd439 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd449 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-421/200)) (c'i := (9433/10000)) (r' := (389/2500)) (E := (1/10000)) (N := (8339/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (507/625)) (c'i := (-27233/10000)) (r' := (7429/10000)) (E := (1/10000)) (N := (23067/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-94883/10000)) (c'i := (-31703/10000)) (r' := (47789/10000)) (E := (1/10000)) (N := (1776/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (100039/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd450 : ∀ z : ℂ, |z.re - (13/16)| ≤ (1/16) → |z.im - (-1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-10369/5000)) (c'i := (1433/1250)) (r' := (1523/10000)) (E := (1/10000)) (N := (163/200)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (641/2500)) (c'i := (-8767/2500)) (r' := (7459/10000)) (E := (1/10000)) (N := (1481/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (35161/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd451 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-3/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-9431/5000)) (c'i := (2241/2500)) (r' := (1773/10000)) (E := (1/10000)) (N := (9561/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (121/5000)) (c'i := (-2667/1250)) (r' := (7729/10000)) (E := (1/10000)) (N := (5221/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-72817/10000)) (c'i := (11447/10000)) (r' := (19499/5000)) (E := (1/10000)) (N := (10669/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (73711/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd452 : ∀ z : ℂ, |z.re - (15/16)| ≤ (1/16) → |z.im - (-1/16)| ≤ (1/16) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-371/200)) (c'i := (2827/2500)) (r' := (1743/10000)) (E := (1/10000)) (N := (2349/2500)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-5677/10000)) (c'i := (-29473/10000)) (r' := (7887/10000)) (E := (1/10000)) (N := (869/400)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-110943/10000)) (c'i := (5743/1250)) (r' := (53621/10000)) (E := (1/10000)) (N := (6003/2000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (120079/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd448 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (-1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd449 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd450 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd451 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd452 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd328 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (-1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd329 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd330 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd331 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd448 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd232 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (-1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd233 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd234 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd235 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd328 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd454 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (1373/1000)) (r' := (1879/5000)) (E := (1/10000)) (N := (221/625)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15279/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd455 : ∀ z : ℂ, |z.re - (1/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-323/100)) (c'i := (1623/1000)) (r' := (6853/10000)) (E := (1/10000)) (N := (3953/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (9037/2500)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd457 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-471/200)) (c'i := (7021/5000)) (r' := (643/2500)) (E := (1/10000)) (N := (3187/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (13709/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd458 : ∀ z : ℂ, |z.re - (5/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-62/25)) (c'i := (1073/625)) (r' := (181/625)) (E := (1/10000)) (N := (7289/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (15081/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd459 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (1/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-99/50)) (c'i := (3667/2500)) (r' := (689/2000)) (E := (1/10000)) (N := (8839/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine U0DiskEscape.escape_step_coords (c'x := (-9611/10000)) (c'i := (-9121/2000)) (r' := (3637/2000)) (E := (1/10000)) (N := (12321/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (23303/5000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd460 : ∀ z : ℂ, |z.re - (7/8)| ≤ (1/8) → |z.im - (3/8)| ≤ (1/8) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-421/200)) (c'i := (9521/5000)) (r' := (1843/5000)) (E := (1/10000)) (N := (119/125)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (1774/625)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd456 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (1/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd457 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd458 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd459 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd460 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd461 : ∀ z : ℂ, |z.re - (3/4)| ≤ (1/4) → |z.im - (3/4)| ≤ (1/4) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him _
    refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him
    refine U0DiskEscape.escape_step_coords (c'x := (-273/100)) (c'i := (2373/1000)) (r' := (4383/5000)) (E := (1/10000)) (N := (10607/10000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    exact U0DiskEscape.escape_terminal_coords (M := (36171/10000)) (Nb := (15009/5000)) (S := (18033/5000)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nd453 : ∀ z : ℂ, |z.re - (1/2)| ≤ (1/2) → |z.im - (1/2)| ≤ (1/2) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd454 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd455 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd456 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd461 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  have nd1 : ∀ z : ℂ, |z.re - (0)| ≤ (1) → |z.im - (0)| ≤ (1) → ‖z‖ ≤ 1 → z ∉ filledJulia (⟨(-273/100), (156/125)⟩ : ℂ) := by
    intro z hre him hz
    rcases U0DiskEscape.interval_split hre with h1 | h1 <;>
      rcases U0DiskEscape.interval_split him with h2 | h2
    · exact nd2 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd11 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd232 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
    · exact nd453 z (by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) (by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) hz
  exact U0DiskEscape.viable_of_root_square nd1

end U0DichotomySlice
