import GaloisForLFunctions.RHTower.VerticalProgressionMollifier
import GaloisForLFunctions.RHTower.ChronologicalHeatMellin
import GaloisForLFunctions.RHTower.FermiNymanFiniteCoefficientError

/-!
# Supported Selberg–Möbius rows in the chronological and Nyman carriers

The row `μ(k) log(N/k)/log N` is supported on `1 ≤ k ≤ N`. Its coefficients
have absolute value at most one, its last coefficient is zero, and each fixed
coefficient tends to `μ(k)`. These properties and finite L² admission are
unconditional. They do not assert convergence of the full error norms.

The same row defines chronological Bose errors and Nyman errors. The exact
dyadic difference of the latter is the corresponding Haar/Fermi error.
-/

open Filter Topology MeasureTheory Set
open GaloisForLFunctions.NymanMellin

namespace RHTower

noncomputable section

/-- Selberg's linear Möbius row, extended by zero outside its finite support. -/
def selbergMobiusCoeff (N k : ℕ) : ℝ :=
  if k ∈ Finset.Icc 1 N then Sieve.linearMollifierCoeff N k else 0

theorem selbergMobiusCoeff_eq {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    selbergMobiusCoeff N k =
      (ArithmeticFunction.moebius k : ℝ) * Real.log ((N : ℝ) / k) / Real.log N := by
  simp only [selbergMobiusCoeff, if_pos hk, Sieve.linearMollifierCoeff]

@[simp] theorem selbergMobiusCoeff_zero (N : ℕ) : selbergMobiusCoeff N 0 = 0 := by
  simp [selbergMobiusCoeff]

theorem selbergMobiusCoeff_eq_zero_of_lt {N k : ℕ} (hk : N < k) :
    selbergMobiusCoeff N k = 0 := by
  simp [selbergMobiusCoeff, not_le.mpr hk]

/-- Every supported Selberg row lies in the unit coefficient box. -/
theorem abs_selbergMobiusCoeff_le_one (N k : ℕ) : |selbergMobiusCoeff N k| ≤ 1 := by
  unfold selbergMobiusCoeff
  split_ifs with hk
  · exact VerticalAP.abs_linearMollifierCoeff_le_one hk
  · simp

theorem selbergMobiusCoeff_one {N : ℕ} (hN : 2 ≤ N) : selbergMobiusCoeff N 1 = 1 := by
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  simp [selbergMobiusCoeff, Sieve.linearMollifierCoeff, hlog, show 1 ≤ N by omega]

/-- The terminal coefficient is suppressed exactly, including degenerate rows. -/
@[simp] theorem selbergMobiusCoeff_self (N : ℕ) : selbergMobiusCoeff N N = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [selbergMobiusCoeff, Sieve.linearMollifierCoeff, hNR]

/-- Damping disappears at every fixed index, although it vanishes at the moving endpoint. -/
theorem tendsto_selbergMobiusCoeff (k : ℕ) :
    Tendsto (fun N : ℕ => selbergMobiusCoeff N k) atTop
      (𝓝 (ArithmeticFunction.moebius k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => Real.log k / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlim : Tendsto (fun N : ℕ => (ArithmeticFunction.moebius k : ℝ) *
      (1 - Real.log k / Real.log N)) atTop (𝓝 (ArithmeticFunction.moebius k : ℝ)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using (hone.sub hsmall).const_mul
      (ArithmeticFunction.moebius k : ℝ)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop k] with N hN hkN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergMobiusCoeff_eq (Finset.mem_Icc.mpr ⟨hk, hkN⟩), Real.log_div hNR hkR]
  field_simp

/-- Chronological Bose error of the supported Selberg row. -/
def selbergChronologicalError (N : ℕ) : ℝ → ℝ :=
  chronologicalHeatError (selbergMobiusCoeff N) N

/-- Nyman error of the same row on the full positive half-line. -/
def selbergNymanError (N : ℕ) : ℝ → ℂ :=
  finiteNymanError N (selbergMobiusCoeff N)

/-- Haar/Fermi error of the same row on the unit interval. -/
def selbergFermiError (N : ℕ) (t : ℝ) : ℂ :=
  dyadicHaar t + ∑ k ∈ Finset.Icc 1 N,
    (selbergMobiusCoeff N k : ℂ) * fermiNymanGen (k : ℝ) t

theorem selbergChronologicalError_memLp (N : ℕ) :
    MemLp (selbergChronologicalError N) 2 chronologicalPositiveVolume :=
  chronologicalHeatError_memLp _ _

theorem integrableOn_normSq_selbergNymanError (N : ℕ) :
    IntegrableOn (fun t => ‖selbergNymanError N t‖ ^ 2) (Ioi (0 : ℝ)) :=
  integrableOn_normSq_finiteNymanError _ _

/-- Exact transfer of the Selberg row to the Fermi–Nyman Haar target. -/
theorem fermiDilationDifference_selbergNymanError (N : ℕ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    fermiDilationDifference (selbergNymanError N) t = selbergFermiError N t :=
  fermiDilationDifference_finiteNymanError _ _ ht

end

end RHTower
