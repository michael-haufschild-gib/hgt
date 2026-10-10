import GaloisForLFunctions.RHTower.PrimeCoShiftKernelProjection
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Escape through unused prime coordinates

Multiplication by primes tending to infinity sends every fixed arithmetic Hilbert vector weakly
to zero. Compact operators kill these translates in norm. Each fixed multiplicative shift and
co-shift commutes with all sufficiently late prime translates.
-/

namespace RHTower.PrimeCoShift

noncomputable section

open Filter Topology GaloisForLFunctions.HTGeometry

/-- A prime strictly beyond each given natural-number cutoff. -/
def paperCoShiftEscapePrime (n : ℕ) : Nat.Primes :=
  ⟨(Nat.exists_infinite_primes (n + 1)).choose,
    (Nat.exists_infinite_primes (n + 1)).choose_spec.2⟩

theorem paperCoShiftEscapePrime_gt (n : ℕ) : n < (paperCoShiftEscapePrime n : ℕ) :=
  (Nat.exists_infinite_primes (n + 1)).choose_spec.1

/-- Escaping prime translates eventually vanish at each fixed coordinate. -/
theorem paperCoShiftEscape_coordinate (v : H) (m : ℕ+) :
    ∀ᶠ n in atTop, Vop (primePNat (paperCoShiftEscapePrime n)) v m = 0 := by
  filter_upwards [eventually_ge_atTop (m : ℕ)] with n hn
  apply Vop_apply_of_not_dvd
  intro hd
  have hle := Nat.le_of_dvd m.property hd
  have hgt := paperCoShiftEscapePrime_gt n
  change (paperCoShiftEscapePrime n : ℕ) ≤ (m : ℕ) at hle
  omega

/-- Escaping prime translates are weakly null for every arithmetic Hilbert vector. -/
theorem paperCoShiftEscape_weak_tendsto (v z : H) :
    Tendsto (fun n => inner ℂ z (Vop (primePNat (paperCoShiftEscapePrime n)) v))
      atTop (𝓝 0) := by
  apply tendsto_inner_lp_of_coord _ (norm_nonneg v)
    (fun n => ((primeShift (primePNat (paperCoShiftEscapePrime n))).norm_map v).le)
  intro m
  have he : (fun n => Vop (primePNat (paperCoShiftEscapePrime n)) v m) =ᶠ[atTop]
      fun _ => (0 : ℂ) := paperCoShiftEscape_coordinate v m
  exact tendsto_const_nhds.congr' he.symm

/-- Every compact correction vanishes along the escaping arithmetic translates. -/
theorem paperCoShiftEscape_compact_tendsto (K : compactOperatorStarAlgebra H) (v : H) :
    Tendsto (fun n => K.1 (Vop (primePNat (paperCoShiftEscapePrime n)) v))
      atTop (𝓝 0) := by
  let C : ℝ := ‖v‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let u : H := ((C⁻¹ : ℝ) : ℂ) • v
  have hu : ‖u‖ ≤ 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hC]
    rw [inv_mul_le_iff₀ hC, mul_one]
    dsimp [C]
    linarith
  have huv : (C : ℂ) • u = v := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hC.ne',
      Complex.ofReal_one, one_smul]
  have ht := tendsto_norm_compact_of_weaklyNull K.1 K.2
    (fun n => Vop (primePNat (paperCoShiftEscapePrime n)) u)
    (fun n => ((primeShift (primePNat (paperCoShiftEscapePrime n))).norm_map u).le.trans hu)
    (fun z => paperCoShiftEscape_weak_tendsto u z)
  have hs := (tendsto_const_nhds (x := (C : ℂ))).smul ht
  simpa only [← map_smul, huv, smul_zero] using hs

/-- Every fixed positive integer is coprime to all sufficiently late escaping primes. -/
theorem paperCoShiftEscape_eventually_coprime (p : ℕ+) :
    ∀ᶠ n in atTop, Nat.Coprime (paperCoShiftEscapePrime n : ℕ) (p : ℕ) := by
  filter_upwards [eventually_ge_atTop (p : ℕ)] with n hn
  apply (paperCoShiftEscapePrime n).property.coprime_iff_not_dvd.mpr
  intro hd
  have hle := Nat.le_of_dvd p.property hd
  change (paperCoShiftEscapePrime n : ℕ) ≤ (p : ℕ) at hle
  have hgt := paperCoShiftEscapePrime_gt n
  omega

/-- Both arithmetic generators commute with every sufficiently remote prime shift. -/
theorem paperCoShiftEscape_eventually_commute (p : ℕ+) :
    ∀ᶠ n in atTop,
      Commute (Vop p) (Vop (primePNat (paperCoShiftEscapePrime n))) ∧
      Commute (Vop p) (primeCoShift (primePNat (paperCoShiftEscapePrime n))) := by
  filter_upwards [paperCoShiftEscape_eventually_coprime p] with n hn
  exact ⟨Vop_commute _ _, (coShift_commute_Vop hn.symm).symm⟩

end

end RHTower.PrimeCoShift
