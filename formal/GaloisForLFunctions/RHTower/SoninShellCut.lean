import GaloisForLFunctions.RHTower.SoninScaledPacketOrthogonality

/-!
# Cutting a shell into equal separated annuli

Dividing `[b,c]` into `N` equal pieces and taking each piece as an annulus gives centres in
arithmetic progression with common half-width `(c-b)/(2N)`.  Consecutive annuli abut rather than
overlap, so the separation the orthogonality needs holds with equality, and every annulus lies
inside the shell.

Since the half-width is below the inner radius whenever the shell starts away from the origin, each
annulus also carries a genuine two-lobe packet, and the whole cut is admissible for the packet
family at once.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory

/-- The half-width of each piece when a shell is cut into `N` equal annuli. -/
def soninShellCutWidth (b c : ℝ) (N : ℕ) : ℝ := (c - b) / (2 * N)

/-- The centre of the `i`-th piece. -/
def soninShellCutCentre (b c : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  b + (2 * ((i : ℕ) : ℝ) + 1) * soninShellCutWidth b c N

theorem soninShellCutWidth_pos (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) :
    0 < soninShellCutWidth b c N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [soninShellCutWidth]
  apply div_pos (by linarith)
  linarith

theorem two_mul_card_mul_soninShellCutWidth (b c : ℝ) {N : ℕ} (hN : 0 < N) :
    2 * (N : ℝ) * soninShellCutWidth b c N = c - b := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [soninShellCutWidth]
  field_simp

theorem soninShellCutCentre_nonneg (b c : ℝ) (hb : 0 < b) (hbc : b < c) {N : ℕ} (hN : 0 < N)
    (i : Fin N) : 0 ≤ soninShellCutCentre b c N i := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hi : (0 : ℝ) ≤ 2 * ((i : ℕ) : ℝ) + 1 := by positivity
  rw [soninShellCutCentre]
  nlinarith [hδ, hi, hb]

/-- The half-width is below the inner radius, so the annulus's two lobes are disjoint. -/
theorem soninShellCutWidth_lt_centre (b c : ℝ) (hb : 0 < b) (hbc : b < c) {N : ℕ} (hN : 0 < N)
    (i : Fin N) : soninShellCutWidth b c N < soninShellCutCentre b c N i := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [soninShellCutCentre]
  nlinarith [hδ, hi, hb]

/-- **Separation.**  Distinct pieces are separated, consecutive ones abutting. -/
theorem soninShellCut_sep (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (i j : Fin N) (hij : i < j) :
    soninShellCutCentre b c N i + soninShellCutWidth b c N ≤
      soninShellCutCentre b c N j - soninShellCutWidth b c N := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
    have : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    exact_mod_cast this
  rw [soninShellCutCentre, soninShellCutCentre]
  nlinarith [hδ, hlt]

/-- Each piece lies inside the shell. -/
theorem soninShellCut_le (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    b ≤ soninShellCutCentre b c N i - soninShellCutWidth b c N ∧
      soninShellCutCentre b c N i + soninShellCutWidth b c N ≤ c := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hiN : ((i : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    have : (i : ℕ) + 1 ≤ N := i.isLt
    exact_mod_cast this
  have htot := two_mul_card_mul_soninShellCutWidth b c hN
  constructor
  · rw [soninShellCutCentre]
    nlinarith [hδ, hi]
  · rw [soninShellCutCentre]
    nlinarith [hδ, hiN, htot]

/-- A small enough reference tail forces the packet mean below one, whatever the annulus. -/
theorem abs_soninScaledPacketMean_le_one (m δ w : ℝ) (hδ : 0 < δ)
    (h : 2 * soninRefTailSup (δ * |w|) ≤ ∫ y : ℝ, soninUnitBumpData y) :
    |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 := by
  have hJ₀ : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  have hbase := abs_soninScaledPacketMean_le_tailSup m δ w hδ
  nlinarith [hbase, h, hJ₀]

/-- **The cut packets are orthonormal.**  A shell cut into `N` equal annuli, all carrying the same
frequency, gives `N` orthonormal normalized packets as soon as the half-width times the carrier is
large enough for the mean and the reference-square tail. -/
theorem orthonormal_soninShellCutPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) {N : ℕ} (hN : 0 < N)
    (w : ℝ)
    (hmean : 2 * soninRefTailSup (soninShellCutWidth b c N * |w|) ≤
      ∫ y : ℝ, soninUnitBumpData y)
    (hSq : soninRefSqTailSup (soninShellCutWidth b c N * |w|) ≤
      (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    Orthonormal ℂ fun i : Fin N =>
      ((‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
              (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖ : ℂ))⁻¹ •
        soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN) :=
  orthonormal_soninScaledPacketEven (fun i => soninShellCutCentre b c N i)
    (fun _ => soninShellCutWidth b c N) (fun _ => w)
    (fun _ => soninShellCutWidth_pos b c hbc hN)
    (fun i => soninShellCutWidth_lt_centre b c hb hbc hN i)
    (fun i => soninShellCutCentre_nonneg b c hb hbc hN i)
    (fun i j hij => soninShellCut_sep b c hbc hN i j hij)
    (fun _ => abs_soninScaledPacketMean_le_one _ _ w (soninShellCutWidth_pos b c hbc hN) hmean)
    (fun _ => hSq)

end RHTower
