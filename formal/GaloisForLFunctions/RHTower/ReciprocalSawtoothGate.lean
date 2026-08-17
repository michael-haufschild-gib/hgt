import GaloisForLFunctions.RHTower.HarmonicPrimitiveMassAdjoint
import GaloisForLFunctions.RHTower.HarmonicTriangularProjection
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# The reciprocal-sawtooth form of the maximal floor path

The maximal-floor path `A_N(D) = ∑_{d ≤ D} R(⌊N/d⌋)` differs from its full-range value by the
triangular transport, so the centred path `B_N(D) = A_N(D) + 2γD` satisfies

`B_N(D) = B_N(N) − T_N(D) − 2γ(N − D)`.

Writing `⌊N/m⌋ = N/m − α_m` with the reciprocal sawtooth `α_m = {N/m}` and summing the harmonic
part by parts turns the transport into one signed two-clock correlation

`T_N(D) = N·S_M + R(M)(α_{M+1} − η) − ∑_{2 ≤ m ≤ M} a_m α_m`,

with `M = ⌊N/(D+1)⌋`, `S_M` the harmonic primitive of `R`, and `η = D − ⌊N/(M+1)⌋`.  The `m = 1`
term drops because `α_1 = 0`.  For the prime source `a_m = Λ(m) − 1` the total variation of the
correlation is `|R(M)| + ∑_{m ≤ M}|a_m| = O(M)`, so the apparent sum of `M` independent floor
errors is a single hyperbola transport in disguise.
-/

open Filter ArithmeticFunction

namespace RHTower

noncomputable section

/-- The maximal-floor path sum `A_N(D) = ∑_{d ≤ D} R(⌊N/d⌋)`. -/
def floorPathSum (a : ℕ → ℝ) (N D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, sourcePartialSum a (N / d)

/-- The centred path sum `B_N(D) = A_N(D) + 2γD`. -/
def floorPathGate (a : ℕ → ℝ) (gam : ℝ) (N D : ℕ) : ℝ :=
  floorPathSum a N D + 2 * gam * (D : ℝ)

/-- **(24.29)** The reciprocal sawtooth `α_m = {N/m}`. -/
def reciprocalSawtooth (N m : ℕ) : ℝ := Int.fract ((N : ℝ) / (m : ℝ))

/-- **(24.29)** The deficit `η = D − ⌊N/(M+1)⌋` of the last quotient fibre. -/
def fibreDeficit (N D : ℕ) : ℝ := (D : ℝ) - ((N / (N / (D + 1) + 1) : ℕ) : ℝ)

theorem natDiv_eq_sub_sawtooth (N m : ℕ) :
    ((N / m : ℕ) : ℝ) = (N : ℝ) / (m : ℝ) - reciprocalSawtooth N m := by
  rw [reciprocalSawtooth, Int.fract, Int.floor_div_natCast]
  simp
  norm_cast

@[simp] theorem reciprocalSawtooth_one (N : ℕ) : reciprocalSawtooth N 1 = 0 := by
  rw [reciprocalSawtooth]
  simp

/-- The sawtooth correlation starts at `m = 2` because `α_1 = 0`. -/
theorem sum_sawtooth_eq_sum_Icc_two (a : ℕ → ℝ) (N M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, a m * reciprocalSawtooth N m
      = ∑ m ∈ Finset.Icc 2 M, a m * reciprocalSawtooth N m := by
  refine (Finset.sum_subset (Finset.Icc_subset_Icc (by omega) (le_refl M)) ?_).symm
  intro x hx hnot
  rw [Finset.mem_Icc] at hx
  have hx1 : x = 1 := by
    by_contra h
    exact hnot (Finset.mem_Icc.2 ⟨by omega, hx.2⟩)
  rw [hx1, reciprocalSawtooth_one, mul_zero]

/-! ## The triangular transport form of the centred path -/

/-- **(24.33)** The centred path is its full-range value minus the triangular transport and the
centring mass of the omitted range. -/
theorem floorPathGate_eq (a : ℕ → ℝ) (gam : ℝ) {N D : ℕ} (hDN : D ≤ N) :
    floorPathGate a gam N D
      = floorPathGate a gam N N - triangularTransport a N D
        - 2 * gam * ((N : ℝ) - (D : ℝ)) := by
  have hsplit : floorPathSum a N N
      = floorPathSum a N D + ∑ d ∈ Finset.Icc (D + 1) N, sourcePartialSum a (N / d) := by
    rw [floorPathSum, floorPathSum]
    have h1 : Finset.Icc 1 D = Finset.Ico 1 (D + 1) := (Finset.Ico_add_one_right_eq_Icc 1 D).symm
    have h2 : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := (Finset.Ico_add_one_right_eq_Icc 1 N).symm
    have h3 : Finset.Icc (D + 1) N = Finset.Ico (D + 1) (N + 1) :=
      (Finset.Ico_add_one_right_eq_Icc (D + 1) N).symm
    rw [h1, h2, h3]
    exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
  rw [floorPathGate, floorPathGate, hsplit, tail_sourcePartialSum_eq_triangularTransport a N D]
  ring

/-! ## The sawtooth form -/

/-- **(24.30)** The reciprocal-sawtooth form of the triangular transport: the floor displacement
splits into the harmonic primitive of the source partial sums, one boundary term carrying the
deficit of the last fibre, and one signed sawtooth correlation. -/
theorem triangularTransport_sawtooth (a : ℕ → ℝ) (N D : ℕ) :
    triangularTransport a N D
      = (N : ℝ) * harmonicPrimitive (sourcePartialSum a) (N / (D + 1))
        + sourcePartialSum a (N / (D + 1))
            * (reciprocalSawtooth N (N / (D + 1) + 1) - fibreDeficit N D)
        - ∑ m ∈ Finset.Icc 2 (N / (D + 1)), a m * reciprocalSawtooth N m := by
  set M : ℕ := N / (D + 1) with hM
  have hprim := harmonicPrimitive_sourcePartialSum a M
  have hstep : ∀ m ∈ Finset.Icc 1 M,
      a m * (((N / m : ℕ) : ℝ) - (D : ℝ))
        = (N : ℝ) * (a m / (m : ℝ)) - a m * reciprocalSawtooth N m - (D : ℝ) * a m := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    rw [natDiv_eq_sub_sawtooth]
    field_simp
  rw [triangularTransport, Finset.sum_congr rfl hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hprim, ← sum_sawtooth_eq_sum_Icc_two, fibreDeficit, ← hM]
  have hMd : ((N / (M + 1) : ℕ) : ℝ) = (N : ℝ) / ((M : ℝ) + 1) - reciprocalSawtooth N (M + 1) := by
    have h := natDiv_eq_sub_sawtooth N (M + 1)
    push_cast at h
    exact h
  have hsrc : sourcePartialSum a M = ∑ m ∈ Finset.Icc 1 M, a m := rfl
  rw [← hsrc, hMd]
  ring

/-- **(24.31)** The centred path in reciprocal-sawtooth coordinates. -/
theorem floorPathGate_sawtooth (a : ℕ → ℝ) (gam : ℝ) {N D : ℕ} (hDN : D ≤ N) :
    floorPathGate a gam N D
      = floorPathGate a gam N N
        - (N : ℝ) * harmonicPrimitive (sourcePartialSum a) (N / (D + 1))
        + sourcePartialSum a (N / (D + 1))
            * (fibreDeficit N D - reciprocalSawtooth N (N / (D + 1) + 1))
        + (∑ m ∈ Finset.Icc 2 (N / (D + 1)), a m * reciprocalSawtooth N m)
        - 2 * gam * ((N : ℝ) - (D : ℝ)) := by
  rw [floorPathGate_eq a gam hDN, triangularTransport_sawtooth a N D]
  ring

/-! ## The variation bound -/

/-- The signed source of the prime path. -/
def primeSawtoothSource (n : ℕ) : ℝ := (vonMangoldt n : ℝ) - 1

theorem sum_abs_primeSawtoothSource_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, |primeSawtoothSource m| ≤ 8 * (M : ℝ) := by
  have hbound : ∀ m ∈ Finset.Icc 1 M,
      |primeSawtoothSource m| ≤ (vonMangoldt m : ℝ) + 1 := by
    intro m _
    rw [primeSawtoothSource, abs_le]
    have hnn : (0 : ℝ) ≤ (vonMangoldt m : ℝ) := vonMangoldt_nonneg
    constructor <;> linarith
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have hpsi : ∑ m ∈ Finset.Icc 1 M, (vonMangoldt m : ℝ) = chebyshevPsi M := rfl
  rw [hpsi]
  have h7 := chebyshevPsi_le_seven M
  have hcard : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by
    have : M + 1 - 1 = M := by omega
    rw [this]
  rw [hcard]
  linarith

theorem abs_sourcePartialSum_primeSawtoothSource_le (M : ℕ) :
    |sourcePartialSum primeSawtoothSource M| ≤ 8 * (M : ℝ) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_abs_primeSawtoothSource_le M)

/-- The total variation of the sawtooth gate is linear: the exact form replaces `M` independent
floor errors by one correlation of size `O(M)`. -/
theorem sawtoothGate_variation_le (M : ℕ) :
    |sourcePartialSum primeSawtoothSource M|
      + ∑ m ∈ Finset.Icc 1 M, |primeSawtoothSource m| ≤ 16 * (M : ℝ) := by
  have h1 := abs_sourcePartialSum_primeSawtoothSource_le M
  have h2 := sum_abs_primeSawtoothSource_le M
  linarith

/-- The sawtooth correlation of the prime path is dominated by the linear variation, since the
sawtooth factors lie in `[0, 1)`. -/
theorem abs_sum_primeSawtooth_correlation_le (N M : ℕ) :
    |∑ m ∈ Finset.Icc 2 M, primeSawtoothSource m * reciprocalSawtooth N m| ≤ 8 * (M : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ m ∈ Finset.Icc 2 M,
      |primeSawtoothSource m * reciprocalSawtooth N m| ≤ |primeSawtoothSource m| := by
    intro m _
    rw [abs_mul]
    have h0 : 0 ≤ reciprocalSawtooth N m := Int.fract_nonneg _
    have h1 : reciprocalSawtooth N m < 1 := Int.fract_lt_one _
    have habs : |reciprocalSawtooth N m| ≤ 1 := by
      rw [abs_of_nonneg h0]
      exact h1.le
    calc |primeSawtoothSource m| * |reciprocalSawtooth N m|
        ≤ |primeSawtoothSource m| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = |primeSawtoothSource m| := mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc (by norm_num : (1 : ℕ) ≤ 2) (le_refl M))
    fun m _ _ => abs_nonneg _) ?_
  exact sum_abs_primeSawtoothSource_le M

end

end RHTower
