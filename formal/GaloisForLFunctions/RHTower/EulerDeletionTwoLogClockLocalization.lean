import GaloisForLFunctions.RHTower.EulerDeletionFourLogClockLocalization

/-!
# Critical two-logarithm localization of the signed EDQ source

At two binary logarithms the coefficient-independent physical leakage need
not vanish, but is already logarithmic. Hence this is the smaller clock that
matters for the cofinal polylogarithmic RH ceiling. The retained field is the
literal signed paired-Möbius quotient, with its original physical fibre mass.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology

namespace RHTower.DeletionResidueMartingale

def twoLogClockThreshold (N : ℕ) : ℕ :=
  2 * (Nat.log2 (N + 1) + 1)

/-- The whole-source high-clock error is logarithmic already at two binary
logarithms. This uses no Möbius cancellation beyond `|μ| ≤ 1`. -/
theorem source_twoLogClockProjection_error_norm_sq_le (N : ℕ) :
    ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N -
      (historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) ≤
      3 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) := by
  let M := N + 1
  let H := Nat.log2 M + 1
  let K := twoLogClockThreshold N
  have hHposNat : 1 ≤ H := by dsimp [H]; omega
  have hKdef : K = 2 * H := rfl
  have hMlt : M < 2 ^ H := by
    dsimp [H]
    exact Nat.lt_log2_self
  have hMpowNat : M ^ 2 ≤ 2 ^ K := by
    calc
      M ^ 2 ≤ (2 ^ H) ^ 2 := by gcongr
      _ = 2 ^ K := by rw [← pow_mul, hKdef]; congr 1; omega
  have hclockNat : M ^ 2 ≤ (K + 1) * clock K :=
    hMpowNat.trans (two_pow_le_mul_clock K)
  have hclock : (M : ℝ) ^ 2 ≤ ((K : ℝ) + 1) * (clock K : ℝ) := by
    exact_mod_cast hclockNat
  have hKboundNat : K + 1 ≤ 3 * H := by omega
  have hKbound : ((K : ℝ) + 1) ≤ 3 * (H : ℝ) := by
    exact_mod_cast hKboundNat
  have hNleM : (N : ℝ) ≤ M := by dsimp [M]; push_cast; linarith
  have hN2 : (N : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) N) (by positivity)).mpr hNleM
  have hHnonneg : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hcross : (N : ℝ) ^ 2 ≤
      3 * (H : ℝ) * ((clock K : ℝ) + 1) := by
    calc
      _ ≤ (M : ℝ) ^ 2 := hN2
      _ ≤ ((K : ℝ) + 1) * (clock K : ℝ) := hclock
      _ ≤ (3 * (H : ℝ)) * (clock K : ℝ) :=
        mul_le_mul_of_nonneg_right hKbound (by positivity)
      _ ≤ 3 * (H : ℝ) * ((clock K : ℝ) + 1) := by nlinarith
  have hsource := source_sub_historyProjection_energy_le_clock_tail
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
    (fun n => by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))) N K
  change _ ≤ 3 * (H : ℝ)
  calc
    _ ≤ (N : ℝ) ^ 2 / ((clock K : ℝ) + 1) := hsource
    _ ≤ 3 * (H : ℝ) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < (clock K : ℝ) + 1)).mpr hcross

/-- The retained low-clock field is still the exact signed arithmetic quotient,
not an absolute-value or endpoint substitute. -/
theorem twoLogClockSourceProjection_apply_eq_pairedMoebiusQuotient (N j : ℕ) :
    ((historySpace (twoLogClockThreshold N)).starProjection
      (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)) j =
      pairedMoebiusQuotient N (twoLogClockThreshold N)
        (j % clock (twoLogClockThreshold N)) := by
  exact historyProjection_source_apply_eq_pairedMoebiusQuotient N
    (twoLogClockThreshold N) j

/-- Any super-logarithmic source energy must occur in the signed two-log-clock
projection: the complete omitted physical energy is at most one logarithm. -/
theorem source_energy_le_twoLogClockProjection_energy_add_log (N : ℕ) :
    ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ ^ (2 : ℕ) ≤
      ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) +
        3 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) := by
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
    (historySpace (twoLogClockThreshold N))
  rw [Submodule.starProjection_orthogonal_val] at hp
  have he := source_twoLogClockProjection_error_norm_sq_le N
  nlinarith

end RHTower.DeletionResidueMartingale
