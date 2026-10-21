import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityPairAtEveryDamping
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeHorizonCrossoverScale
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovMoebius
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.HTGeometry.PowerSeriesTailBound
import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable
import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation

/-!
# The receiver is bounded in the zero-free band below half damping

For the damped Möbius row `c_ε(d) = μ(d) d^{-ε}` with mean `m_ε = Σ_d c_ε(d)/d = 1/ζ(1+ε)` the centred
prefix is `A_ε(n) = Σ_{j ≤ n} Σ_{d | j} c_ε(d) - m_ε n` and the receiver energy is
`E_T(ε) = Σ_{n ≤ T} A_ε(n)²/(n(n+1))`. It is bounded for `ε ≥ 1/2`; a horizon-uniform bound at one
fixed `ε < 1/2` is a zero-free half-plane.

**Rate transfer.** If the partial sums of a sign pattern `s` with `|s| ≤ 1` satisfy `|S(x)| ≤ Lx` from
`D` on, summation by parts against the antitone weights `d^{-ε}` and `d^{-1-ε}` in the hyperbola split
of `A` at `D` gives, for `1/4 ≤ ε ≤ 1/2`,

`|A(n)| ≤ 3 D^{1-ε} + 31 L n D^{-ε}`.

**The band.** The Vinogradov–Korobov bound gives `|M(x)| ≤ B x e^{-√(log x)/12}`. Splitting at
`D = n e^{-√(log n)/20}` yields `|A_ε(n)| ≤ K n^{1-ε} e^{-√(log n)/40}` uniformly in `ε ∈ [1/4, 1/2]`,
and on the band `ε ≥ 1/2 - 1/(80 √(log T))` the factor `n^{1-2ε} ≤ e^{√(log n)/40}` is absorbed for
every `n ≤ T`. Hence `E_T(ε)` is bounded uniformly in `T` and in `ε` on the band
(`exists_receiver_le_on_zeroFreeBand`), and so is the Bézout interior energy.

The damping at which the receiver is controlled thus moves from `1/2` to `1/2 - c/√(log T)` at
horizon `T`, paid by the zero-free region; a band of fixed width would be a zero-free strip. The
bound does not reach any fixed `ε < 1/2`.
-/

open Finset Filter Topology
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Summation by parts against linearly growing partial sums -/

/-- Summation by parts on `(D, X]` with `S(x) = Σ_{e ≤ x} s(e)`:
`Σ_{D<d≤X} s(d)w(d) = S(X)w(X+1) - S(D)w(D+1) + Σ_{D<d≤X} S(d)(w(d) - w(d+1))`. -/
theorem sum_Ioc_mul_eq_partialSums (s w : ℕ → ℝ) {D X : ℕ} (hDX : D ≤ X) :
    ∑ d ∈ Ioc D X, s d * w d =
      (∑ e ∈ Icc 1 X, s e) * w (X + 1) - (∑ e ∈ Icc 1 D, s e) * w (D + 1) +
        ∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1)) := by
  induction X, hDX using Nat.le_induction with
  | base => simp
  | succ X hDX ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- **Abel's inequality with linearly growing partial sums.** If `|S(x)| ≤ Lx` for `D ≤ x ≤ X` and
`w ≥ 0` decreases beyond `D`, then `|Σ_{D<d≤X} s(d)w(d)| ≤ L (2D w(D+1) + Σ_{D<d≤X} w(d))`. -/
theorem abs_sum_Ioc_mul_le_of_linear {s w : ℕ → ℝ} {L : ℝ} {D X : ℕ} (hDX : D ≤ X)
    (hS : ∀ x, D ≤ x → x ≤ X → |∑ e ∈ Icc 1 x, s e| ≤ L * x)
    (hw0 : ∀ d, 0 ≤ w d) (hwa : ∀ d, D < d → w (d + 1) ≤ w d) :
    |∑ d ∈ Ioc D X, s d * w d| ≤ L * (2 * D * w (D + 1) + ∑ d ∈ Ioc D X, w d) := by
  rw [sum_Ioc_mul_eq_partialSums s w hDX]
  -- the identity for `s ≡ 1` evaluates `Σ d (w(d) - w(d+1))`
  have hone := sum_Ioc_mul_eq_partialSums (fun _ => (1 : ℝ)) w hDX
  simp only [one_mul, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel] at hone
  have hterm : ∀ d ∈ Ioc D X, |(∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1))| ≤
      L * ((d : ℝ) * (w d - w (d + 1))) := by
    intro d hd
    rw [mem_Ioc] at hd
    have hwd : 0 ≤ w d - w (d + 1) := sub_nonneg.mpr (hwa d hd.1)
    rw [abs_mul, abs_of_nonneg hwd, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hS d hd.1.le hd.2) hwd
  have h1 := mul_le_mul_of_nonneg_right (hS X hDX le_rfl) (hw0 (X + 1))
  have h2 := mul_le_mul_of_nonneg_right (hS D le_rfl hDX) (hw0 (D + 1))
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  rw [← mul_sum] at hsum
  have htri : |(∑ e ∈ Icc 1 X, s e) * w (X + 1) - (∑ e ∈ Icc 1 D, s e) * w (D + 1) +
        ∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1))| ≤
      |∑ e ∈ Icc 1 X, s e| * w (X + 1) + |∑ e ∈ Icc 1 D, s e| * w (D + 1) +
        |∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1))| := by
    have ha := abs_add_le ((∑ e ∈ Icc 1 X, s e) * w (X + 1) - (∑ e ∈ Icc 1 D, s e) * w (D + 1))
      (∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1)))
    have hb := abs_sub ((∑ e ∈ Icc 1 X, s e) * w (X + 1)) ((∑ e ∈ Icc 1 D, s e) * w (D + 1))
    rw [abs_mul, abs_of_nonneg (hw0 _), abs_mul, abs_of_nonneg (hw0 _)] at hb
    linarith
  have hfin : L * X * w (X + 1) + L * D * w (D + 1) +
      L * ∑ d ∈ Ioc D X, (d : ℝ) * (w d - w (d + 1)) =
      L * (2 * D * w (D + 1) + ∑ d ∈ Ioc D X, w d) := by
    rw [hone]; ring
  linarith

/-! ## §2. Damped Möbius-type sums under a linear partial-sum bound -/

/-- `Σ_{e ≤ x} d^{-α} ≤ 3 x^{1-α}` for `0 < α ≤ 1/2`, `x ≥ 1`. -/
theorem sum_Icc_rpow_neg_le_three {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 2) {x : ℕ} (hx : 1 ≤ x) :
    ∑ d ∈ Icc 1 x, (d : ℝ) ^ (-α) ≤ 3 * (x : ℝ) ^ (1 - α) := by
  have h := RHTower.sum_rpow_neg_head_le hα0 (by linarith) x
  have h1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 - α) :=
    Real.one_le_rpow (by exact_mod_cast hx) (by linarith)
  have h2 : (x : ℝ) ^ (1 - α) / (1 - α) ≤ 2 * (x : ℝ) ^ (1 - α) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- **Blocks.** If `|S(x)| ≤ Lx` from `D ≥ 1` on and `|s| ≤ 1`, then for `D ≤ X` and
`0 < α ≤ 1/2`, `|Σ_{D<d≤X} s(d) d^{-α}| ≤ 5 L X^{1-α}`. -/
theorem abs_sum_Ioc_rpow_le_of_linear {s : ℕ → ℝ} {L α : ℝ} {D X : ℕ} (hD : 1 ≤ D) (hDX : D ≤ X)
    (hL : 0 ≤ L) (hα0 : 0 < α) (hα : α ≤ 1 / 2)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
    |∑ d ∈ Ioc D X, s d * (d : ℝ) ^ (-α)| ≤ 5 * L * (X : ℝ) ^ (1 - α) := by
  rcases hDX.eq_or_lt with rfl | hlt
  · simp only [Ioc_self, sum_empty, abs_zero]
    have : 0 ≤ (D : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hab := abs_sum_Ioc_mul_le_of_linear (s := s) (w := fun d : ℕ => (d : ℝ) ^ (-α)) hDX
    (fun x hx _ => hS x hx) (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (fun d hd => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < d))
      (by exact_mod_cast (Nat.le_succ d)) (by linarith))
  have hX1 : 1 ≤ X := by omega
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  -- `D (D+1)^{-α} ≤ (D+1)^{1-α} ≤ X^{1-α}`
  have hhead : (D : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-α) ≤ (X : ℝ) ^ (1 - α) := by
    have hD1 : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
    have e1 : ((D + 1 : ℕ) : ℝ) ^ (1 - α) = ((D + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-α) := by
      rw [show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add hD1, Real.rpow_one]
    have e2 : (D : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-α) ≤ ((D + 1 : ℕ) : ℝ) ^ (1 - α) := by
      rw [e1]
      exact mul_le_mul_of_nonneg_right (by push_cast; linarith)
        (Real.rpow_nonneg hD1.le _)
    exact e2.trans (Real.rpow_le_rpow hD1.le (by exact_mod_cast hlt) (by linarith))
  have htail : ∑ d ∈ Ioc D X, (d : ℝ) ^ (-α) ≤ 3 * (X : ℝ) ^ (1 - α) := by
    refine le_trans ?_ (sum_Icc_rpow_neg_le_three hα0 hα hX1)
    refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ =>
      Real.rpow_nonneg (Nat.cast_nonneg d) _
    rw [mem_Ioc] at hd; rw [mem_Icc]; omega
  calc _ ≤ L * (2 * D * ((D + 1 : ℕ) : ℝ) ^ (-α) + ∑ d ∈ Ioc D X, (d : ℝ) ^ (-α)) := by
        simpa using hab
    _ ≤ L * (2 * (X : ℝ) ^ (1 - α) + 3 * (X : ℝ) ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left (by linarith) hL
    _ = 5 * L * (X : ℝ) ^ (1 - α) := by ring

/-- `Σ_{D<d≤X} d^{-1-ε} ≤ D^{-ε}/ε` for `D ≥ 1`. -/
theorem sum_Ioc_rpow_neg_one_sub_le {ε : ℝ} (hε : 0 < ε) {D X : ℕ} (hD : 1 ≤ D) :
    ∑ d ∈ Ioc D X, (d : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) ^ (-ε) / ε := by
  rcases le_or_gt X D with hXD | hDX
  · rw [Ioc_eq_empty (by omega), sum_empty]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hε.le
  obtain ⟨K, rfl⟩ : ∃ K, X = D + K := ⟨X - D, by omega⟩
  rw [dampedSign_sum_Ioc_eq_sum_range_shift]
  have h := sum_shift_rpow_tail_le (s := 1 + ε) (by linarith) (D - 1) K
  have hJ : ((D - 1 : ℕ) : ℝ) + 1 = D := by
    rw [Nat.cast_sub hD]; push_cast; ring
  rw [hJ, show (1 : ℝ) - (1 + ε) = -ε by ring, show (1 + ε) - 1 = ε by ring] at h
  refine le_trans (le_of_eq (sum_congr rfl fun i _ => ?_)) h
  congr 1
  push_cast
  ring

/-- **Tails.** If `|S(x)| ≤ Lx` from `D ≥ 1` on and `|s| ≤ 1`, then for `ε > 0`,
`|Σ_{d>D} s(d) d^{-1-ε}| ≤ (2 + 1/ε) L D^{-ε}`. -/
theorem abs_tsum_tail_rpow_le_of_linear {s : ℕ → ℝ} {L ε : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (hL : 0 ≤ L) (hε : 0 < ε) (hs1 : ∀ d, |s d| ≤ 1)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
    Summable (fun i : ℕ => ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))) ∧
      |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))| ≤
        (2 + 1 / ε) * L * (D : ℝ) ^ (-ε) := by
  have hp : Summable (fun i : ℕ => ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε))) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(1 + ε))) (D + 1)).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hsum : Summable (fun i : ℕ => ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))) := by
    refine hp.of_norm_bounded fun i => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hs1 _)
  refine ⟨hsum, le_of_tendsto' hsum.hasSum.tendsto_sum_nat.abs fun K => ?_⟩
  have hshift : ∑ i ∈ range K, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) =
      ∑ d ∈ Ioc D (D + K), s d * (d : ℝ) ^ (-(1 + ε)) := by
    rw [dampedSign_sum_Ioc_eq_sum_range_shift]
    exact sum_congr rfl fun i _ => mul_comm _ _
  rw [hshift]
  have hab := abs_sum_Ioc_mul_le_of_linear (s := s) (w := fun d : ℕ => (d : ℝ) ^ (-(1 + ε)))
    (Nat.le_add_right D K) (fun x hx _ => hS x hx) (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (fun d hd => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < d))
      (by exact_mod_cast (Nat.le_succ d)) (by linarith))
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hhead : (D : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) ^ (-ε) := by
    have hle : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) ^ (-(1 + ε)) :=
      Real.rpow_le_rpow_of_nonpos hD0 (by push_cast; linarith) (by linarith)
    have he : (D : ℝ) * (D : ℝ) ^ (-(1 + ε)) = (D : ℝ) ^ (-ε) := by
      rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hD0.ne']
      field_simp
    calc (D : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) * (D : ℝ) ^ (-(1 + ε)) :=
          mul_le_mul_of_nonneg_left hle hD0.le
      _ = _ := he
  have htail := sum_Ioc_rpow_neg_one_sub_le hε (X := D + K) hD
  calc _ ≤ L * (2 * D * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) +
          ∑ d ∈ Ioc D (D + K), (d : ℝ) ^ (-(1 + ε))) := by simpa using hab
    _ ≤ L * (2 * (D : ℝ) ^ (-ε) + (D : ℝ) ^ (-ε) / ε) :=
        mul_le_mul_of_nonneg_left (by linarith) hL
    _ = (2 + 1 / ε) * L * (D : ℝ) ^ (-ε) := by ring

/-! ## §3. The hyperbola bound with a linear partial-sum rate -/

theorem summable_dampedSignWeight_div_of_abs_le_one {s : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hs1 : ∀ d, |s d| ≤ 1) : Summable (fun d : ℕ => dampedSignWeight s ε d / d) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).of_norm_bounded fun d => ?_
  rw [dampedSignWeight_div hε, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hs1 _)

/-- **The rate hyperbola bound.** If `|s| ≤ 1` and `|S(x)| ≤ Lx` for `x ≥ D`, then for
`1 ≤ D ≤ n` and `1/4 ≤ ε ≤ 1/2`, `|A(n)| ≤ 3 D^{1-ε} + 31 L n D^{-ε}`, where `A` is the centred
prefix of `c = s d^{-ε}` with its own mean. -/
theorem abs_weightCenteredPrefix_dampedSign_le_of_linear {s : ℕ → ℝ} {L ε : ℝ} (hL : 0 ≤ L)
    (hε4 : 1 / 4 ≤ ε) (hε2 : ε ≤ 1 / 2) (hs1 : ∀ d, |s d| ≤ 1) {n D : ℕ} (hD : 1 ≤ D)
    (hDn : D ≤ n) (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      3 * (D : ℝ) ^ (1 - ε) + 31 * L * n * (D : ℝ) ^ (-ε) := by
  have hε : 0 < ε := by linarith
  set c := dampedSignWeight s ε
  have hsum := summable_dampedSignWeight_div_of_abs_le_one hε hs1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- the mean splits at `D`
  have hmean : ∑' d : ℕ, c d / d = ∑ d ∈ Icc 1 D, c d / d +
      ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [← hsum.sum_add_tsum_nat_add (D + 1), dampedSign_sum_range_succ_eq_add_Icc]
    simp [c, dampedSignWeight]
  -- the floor sum splits at `D`
  have hsplit : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) + ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) := by
    have h1 : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    have h2 : Icc 1 D = Ioc 0 D := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [h1, h2, sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  -- long moduli counted along the cofactor
  have hlong : ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d := by
    have hcount : ∀ d, c d * ((n / d : ℕ) : ℝ) = ∑ _k ∈ Icc 1 (n / d), c d := fun d => by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]; simp
    simp_rw [hcount]
    refine sum_comm' fun d k => ?_
    simp only [mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hDd, hdn⟩, hk1, hkd⟩
      have hd0 : 0 < d := by omega
      have hkd' : k * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp hkd
      refine ⟨⟨hDd, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm k d])⟩,
        hk1, le_trans hkd (Nat.div_le_self n d)⟩
    · rintro ⟨⟨hDd, hdk⟩, hk1, hkn⟩
      have hd0 : 0 < d := by omega
      have hdk' : d * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hdk
      refine ⟨⟨hDd, le_trans hdk (Nat.div_le_self n k)⟩, hk1,
        (Nat.le_div_iff_mul_le hd0).mpr (by linarith [mul_comm k d])⟩
  -- piece (a): short moduli
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤
      3 * (D : ℝ) ^ (1 - ε) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ (d : ℝ) ^ (-ε) := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hfl1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hfl2 : (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) := by
        have h := Nat.lt_div_mul_add (a := n) (show 0 < d by omega)
        have h' : (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
        rw [div_sub_one hd0.ne', div_lt_iff₀ hd0]; linarith
      have hc : |c d| ≤ (d : ℝ) ^ (-ε) := by
        rw [show c d = s d * (d : ℝ) ^ (-ε) from rfl, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
      have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) = c d * (((n / d : ℕ) : ℝ) - n / d) := by
        field_simp
      rw [heq, abs_mul]
      have hfr : |((n / d : ℕ) : ℝ) - n / d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      exact (mul_le_mul hc hfr (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans
        (le_of_eq (mul_one _))
    exact (sum_le_sum hterm).trans (sum_Icc_rpow_neg_le_three hε hε2 hD)
  -- piece (b): long moduli, one Abel block per cofactor
  have hb : |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| ≤ 25 * L * n * (D : ℝ) ^ (-ε) := by
    have hblock : ∀ k ∈ Icc 1 n, |∑ d ∈ Ioc D (n / k), c d| ≤
        (if D + 1 ≤ n / k then 5 * L * (n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε)) else 0) := by
      intro k hk
      rw [mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      split_ifs with h
      · have h5 := abs_sum_Ioc_rpow_le_of_linear (X := n / k) hD (by omega) hL hε hε2 hS
        have hX : ((n / k : ℕ) : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε)) := by
          have hle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
          calc ((n / k : ℕ) : ℝ) ^ (1 - ε) ≤ ((n : ℝ) / k) ^ (1 - ε) :=
                Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith)
            _ = (n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε)) := by
                rw [Real.div_rpow hn0.le hk0.le, Real.rpow_neg hk0.le, div_eq_mul_inv]
        calc |∑ d ∈ Ioc D (n / k), c d| = |∑ d ∈ Ioc D (n / k), s d * (d : ℝ) ^ (-ε)| := rfl
          _ ≤ 5 * L * ((n / k : ℕ) : ℝ) ^ (1 - ε) := h5
          _ ≤ 5 * L * ((n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε))) := by gcongr
          _ = _ := by ring
      · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hblock).trans ?_)
    rw [← sum_filter, ← mul_sum]
    -- the cofactors with a nonempty block satisfy `k ≤ n/(D+1)`
    set K := n / (D + 1)
    have hsub : filter (fun k => D + 1 ≤ n / k) (Icc 1 n) ⊆ Icc 1 K := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk ⊢
      refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
      have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hk.2
      linarith [mul_comm k (D + 1)]
    have hKle : (K : ℝ) ≤ (n : ℝ) / D := by
      calc (K : ℝ) ≤ (n : ℝ) / ((D + 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ (n : ℝ) / D := div_le_div_of_nonneg_left hn0.le hD0 (by push_cast; linarith)
    have hnD1 : (1 : ℝ) ≤ (n : ℝ) / D := by
      rw [le_div_iff₀ hD0, one_mul]; exact_mod_cast hDn
    have hksum : ∑ k ∈ filter (fun k => D + 1 ≤ n / k) (Icc 1 n), (k : ℝ) ^ (-(1 - ε)) ≤
        5 * ((n : ℝ) / D) ^ ε := by
      have h1 : ∑ k ∈ filter (fun k => D + 1 ≤ n / k) (Icc 1 n), (k : ℝ) ^ (-(1 - ε)) ≤
          ∑ k ∈ Icc 1 K, (k : ℝ) ^ (-(1 - ε)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
      have h2 := RHTower.sum_rpow_neg_head_le (c := 1 - ε) (by linarith) (by linarith) K
      rw [show (1 : ℝ) - (1 - ε) = ε by ring] at h2
      have h3 : (K : ℝ) ^ ε ≤ ((n : ℝ) / D) ^ ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hKle hε.le
      have h4 : (1 : ℝ) ≤ ((n : ℝ) / D) ^ ε := Real.one_le_rpow hnD1 hε.le
      have h5 : (K : ℝ) ^ ε / ε ≤ 4 * ((n : ℝ) / D) ^ ε := by
        rw [div_le_iff₀ hε]; nlinarith [Real.rpow_nonneg (Nat.cast_nonneg K) ε]
      linarith
    have hpow : (n : ℝ) ^ (1 - ε) * ((n : ℝ) / D) ^ ε = n * (D : ℝ) ^ (-ε) := by
      rw [Real.div_rpow hn0.le hD0.le, Real.rpow_neg hD0.le, mul_div_assoc', ← Real.rpow_add hn0,
        show 1 - ε + ε = 1 by ring, Real.rpow_one, div_eq_mul_inv]
    have hcoef : 0 ≤ 5 * L * (n : ℝ) ^ (1 - ε) := by
      have := Real.rpow_nonneg hn0.le (1 - ε); positivity
    calc 5 * L * (n : ℝ) ^ (1 - ε) *
          ∑ k ∈ filter (fun k => D + 1 ≤ n / k) (Icc 1 n), (k : ℝ) ^ (-(1 - ε))
        ≤ 5 * L * (n : ℝ) ^ (1 - ε) * (5 * ((n : ℝ) / D) ^ ε) :=
          mul_le_mul_of_nonneg_left hksum hcoef
      _ = 25 * L * ((n : ℝ) ^ (1 - ε) * ((n : ℝ) / D) ^ ε) := by ring
      _ = 25 * L * n * (D : ℝ) ^ (-ε) := by rw [hpow]; ring
  -- piece (c): the tail of the mean
  have hc : |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| ≤
      6 * L * n * (D : ℝ) ^ (-ε) := by
    have ht := (abs_tsum_tail_rpow_le_of_linear hD hL hε hs1 hS).2
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) :=
      tsum_congr fun i => dampedSignWeight_div hε _
    have h6 : (2 + 1 / ε) ≤ 6 := by
      have : 1 / ε ≤ 4 := by rw [div_le_iff₀ hε]; linarith
      linarith
    have hDp : 0 ≤ L * (D : ℝ) ^ (-ε) := mul_nonneg hL (Real.rpow_nonneg hD0.le _)
    rw [heq, abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))|
        ≤ n * ((2 + 1 / ε) * L * (D : ℝ) ^ (-ε)) := mul_le_mul_of_nonneg_left ht hn0.le
      _ ≤ n * (6 * (L * (D : ℝ) ^ (-ε))) := by
          rw [mul_assoc (2 + 1 / ε)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 hDp) hn0.le
      _ = 6 * L * n * (D : ℝ) ^ (-ε) := by ring
  -- assemble
  have hA : weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      (∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d -
          (n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hsplit, hlong, hmean]
    ring
  rw [hA]
  calc _ ≤ |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| +
        |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| +
          |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-! ## §4. The Mertens function at the de la Vallée Poussin rate -/

theorem sum_range_moebius_eq_sum_Icc_moebiusReal (x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), (ArithmeticFunction.moebius n : ℝ) =
      ∑ e ∈ Icc 1 x, moebiusReal e := by
  rw [dampedSign_sum_range_succ_eq_add_Icc]
  simp [moebiusReal]

/-- **The de la Vallée Poussin rate, from Vinogradov–Korobov.** There are `B ≥ 0` and `N₀` with
`|Σ_{e ≤ x} μ(e)| ≤ B x e^{-√(log x)/12}` for every `x ≥ N₀`. -/
theorem exists_abs_sum_moebiusReal_le_sqrtLog :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
      |∑ e ∈ Icc 1 x, moebiusReal e| ≤ B * x * Real.exp (-(Real.sqrt (Real.log x) / 12)) := by
  obtain ⟨B, hB, hev⟩ := RHTower.Sieve.exists_abs_sum_moebius_le_vk_rate
  have hall := tendsto_natCast_atTop_atTop.eventually
    (hev.and (RHTower.Sieve.eventually_vk_conditions one_pos 0))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨B, hB, N₀, fun x hx => ?_⟩
  obtain ⟨h1, hc⟩ := hN₀ x hx
  obtain ⟨-, -, -, -, hLg2, -⟩ := hc
  rw [Nat.floor_natCast, sum_range_moebius_eq_sum_Icc_moebiusReal] at h1
  rw [RHTower.Sieve.log_vkHeight] at hLg2
  have hexp : Real.exp (-(RHTower.Sieve.vkKappa * RHTower.Sieve.vkScale x / 24)) ≤
      Real.exp (-(Real.sqrt (Real.log x) / 12)) := Real.exp_le_exp.mpr (by linarith)
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  exact h1.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-! ## §5. The damped Möbius prefix in the zero-free region -/

theorem abs_moebiusReal_le_one' (d : ℕ) : |moebiusReal d| ≤ 1 := by
  unfold moebiusReal
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem pmPowerDampedRealWeight_eq_dampedSignWeight (ε : ℝ) :
    pmPowerDampedRealWeight ε = dampedSignWeight moebiusReal ε := rfl

theorem dampedDensity_eq_tsum {ε : ℝ} (hε : 0 < ε) :
    dampedDensity ε = ∑' d : ℕ, dampedSignWeight moebiusReal ε d / d :=
  (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq.symm

/-- **The prefix in the zero-free region.** There are `K` and `N₁` with
`|A_ε(n)| ≤ K n^{1-ε} e^{-√(log n)/40}` for every `n ≥ N₁` and every `ε ∈ [1/4, 1/2]`: the split
point `D = ⌊n e^{-√(log n)/20}⌋` makes both the short moduli and the Mertens-rate blocks small. -/
theorem exists_abs_weightCenteredPrefix_pmPowerDamped_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ, ∀ ε : ℝ, 1 / 4 ≤ ε → ε ≤ 1 / 2 → ∀ n : ℕ, N₁ ≤ n →
      |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
        K * (n : ℝ) ^ (1 - ε) * Real.exp (-(Real.sqrt (Real.log n) / 40)) := by
  obtain ⟨B, hB, N₀, hM⟩ := exists_abs_sum_moebiusReal_le_sqrtLog
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((hlog.eventually_ge_atTop 4).and (hlog.eventually_ge_atTop (9 / 4 * Real.log (N₀ + 2))))
  refine ⟨3 + 62 * B, by positivity, N₁, fun ε hε4 hε2 n hn => ?_⟩
  have hε : 0 < ε := by linarith
  obtain ⟨hℓ4, hℓN⟩ := hN₁ n hn
  set ℓ := Real.log n with hℓdef
  set u := Real.sqrt ℓ with hudef
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hℓdef, this, Real.log_zero] at hℓ4; linarith
  have huu : u ^ 2 = ℓ := Real.sq_sqrt (by linarith)
  have hu2 : 2 ≤ u := by
    rw [hudef, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hℓ4
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the split point
  set y := Real.exp (ℓ - u / 20) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = ℓ - u / 20 := Real.log_exp _
  have hkey : 4 / 9 * ℓ ≤ ℓ - u / 20 - Real.log 2 := by nlinarith
  have hN2 : (0 : ℝ) < (N₀ : ℝ) + 2 := by positivity
  have hy2 : (N₀ : ℝ) + 2 ≤ y / 2 := by
    have h := Real.exp_le_exp.mpr (show Real.log ((N₀ : ℝ) + 2) ≤ ℓ - u / 20 - Real.log 2 by
      linarith)
    rwa [Real.exp_log hN2, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  set D := ⌊y⌋₊ with hDdef
  have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyD : y / 2 ≤ (D : ℝ) := by
    have := Nat.lt_floor_add_one y
    linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hDN₀ : N₀ ≤ D := by
    have : (N₀ : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hDn : D ≤ n := by
    have hyn : y ≤ n := by
      rw [hydef, ← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by rw [← hℓdef]; linarith [Real.sqrt_nonneg ℓ])
    exact_mod_cast hDy.trans hyn
  have hlogD_le : Real.log D ≤ ℓ - u / 20 := by
    rw [← hlogy]; exact Real.log_le_log hD0 hDy
  have hlogD_ge : ℓ - u / 20 - Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by positivity) hyD
    rwa [Real.log_div hy0.ne' (by norm_num), hlogy] at h
  -- the Mertens rate is antitone, so it is frozen at `D` from `D` on
  have hsqD : 2 / 3 * u ≤ Real.sqrt (Real.log D) := by
    have h49 : (2 / 3 * u) ^ 2 = 4 / 9 * ℓ := by rw [mul_pow, huu]; ring
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / 3 * u), h49]
    exact Real.sqrt_le_sqrt (by linarith)
  set L := B * Real.exp (-(Real.sqrt (Real.log D) / 12)) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ L * x := by
    intro x hx
    have hxR : (D : ℝ) ≤ x := by exact_mod_cast hx
    have hmono : Real.exp (-(Real.sqrt (Real.log x) / 12)) ≤
        Real.exp (-(Real.sqrt (Real.log D) / 12)) :=
      Real.exp_le_exp.mpr (by
        have := Real.sqrt_le_sqrt (Real.log_le_log hD0 hxR)
        linarith)
    calc _ ≤ B * x * Real.exp (-(Real.sqrt (Real.log x) / 12)) := hM x (hDN₀.trans hx)
      _ ≤ B * x * Real.exp (-(Real.sqrt (Real.log D) / 12)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = L * x := by rw [hLdef]; ring
  have hhyp := abs_weightCenteredPrefix_dampedSign_le_of_linear hL0 hε4 hε2
    (fun d => abs_moebiusReal_le_one' d) hD1 hDn hS
  rw [← dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight] at hhyp
  -- exponential forms of the two pieces
  have hnpow : (n : ℝ) ^ (1 - ε) = Real.exp (ℓ * (1 - ε)) := Real.rpow_def_of_pos hn0 _
  have hshort : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  have hlong : (n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(Real.sqrt (Real.log D) / 12)) ≤
      2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_log hn0, ← hℓdef, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  calc _ ≤ 3 * (D : ℝ) ^ (1 - ε) + 31 * L * n * (D : ℝ) ^ (-ε) := hhyp
    _ = 3 * (D : ℝ) ^ (1 - ε) +
          31 * B * ((n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(Real.sqrt (Real.log D) / 12))) := by
        rw [hLdef]; ring
    _ ≤ 3 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) +
          31 * B * (2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)))) := by
        gcongr
    _ = (3 + 62 * B) * (n : ℝ) ^ (1 - ε) * Real.exp (-(Real.sqrt (Real.log n) / 40)) := by
        rw [hudef, hℓdef]; ring

/-- The trivial prefix bound `|A_ε(n)| ≤ 3 + 31 n` (`D = 1`, partial sums at most `x`). -/
theorem abs_weightCenteredPrefix_pmPowerDamped_le_trivial {ε : ℝ} (hε4 : 1 / 4 ≤ ε)
    (hε2 : ε ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤ 3 + 31 * n := by
  have hS : ∀ x, 1 ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ 1 * x := fun x _ => by
    rw [one_mul]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ Icc 1 x, |moebiusReal e| ≤ ∑ _e ∈ Icc 1 x, (1 : ℝ) :=
          sum_le_sum fun e _ => abs_moebiusReal_le_one' e
      _ = x := by simp
  have h := abs_weightCenteredPrefix_dampedSign_le_of_linear zero_le_one hε4 hε2
    (fun d => abs_moebiusReal_le_one' d) le_rfl hn hS
  rw [← dampedDensity_eq_tsum (by linarith), ← pmPowerDampedRealWeight_eq_dampedSignWeight] at h
  simpa using h

/-! ## §6. The receiver on the zero-free band -/

/-- **The receiver is bounded on the zero-free band below half damping.** There is `E` such that
`E_T(ε) ≤ E` for every horizon `T` and every damping `ε` with `1/4 ≤ ε ≤ 1/2` and
`ε ≥ 1/2 - 1/(80 √(log T))`. -/
theorem exists_receiver_le_on_zeroFreeBand :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        RHTower.pmPowerDampedDivisorDiscreteEnergy ε T ≤ E := by
  obtain ⟨K, hK, N₁, hpre⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le
  have hsum := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show (0 : ℝ) < 1 / 40 by norm_num)
  set S := ∑' m : ℕ, Real.exp (-(1 / 40 * Real.sqrt (Real.log m))) / m
  refine ⟨(N₁ : ℝ) * (3 + 31 * N₁) ^ 2 + K ^ 2 * S, fun T ε hε4 hε2 hband => ?_⟩
  rw [← weightPronicEnergy_pmPowerDamped, weightPronicEnergy]
  set f := fun n : ℕ => weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1)) with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hfdef]; positivity
  -- split the horizon at `N₁`
  have hsplit : ∑ n ∈ Icc 1 T, f n ≤
      ∑ n ∈ Icc 1 T with n < N₁, f n + ∑ n ∈ Icc 1 T with ¬ n < N₁, f n :=
    (sum_filter_add_sum_filter_not _ _ _).ge
  -- small `n`: the trivial bound
  have hsmall : ∑ n ∈ Icc 1 T with n < N₁, f n ≤ (N₁ : ℝ) * (3 + 31 * N₁) ^ 2 := by
    have hsub : (Icc 1 T).filter (fun n => n < N₁) ⊆ range N₁ := fun n hn => by
      simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n < N₁), f n ≤ (3 + 31 * N₁) ^ 2 := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hA := abs_weightCenteredPrefix_pmPowerDamped_le_trivial hε4 hε2 hn.1.1
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (3 + 31 * N₁) ^ 2 := by
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) (hA.trans ?_) 2
        have : (n : ℝ) ≤ N₁ := by exact_mod_cast hn.2.le
        linarith
      simp only [hfdef]
      rw [div_le_iff₀ (by positivity)]
      exact hA2.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith))
    calc ∑ n ∈ Icc 1 T with n < N₁, f n ≤ ∑ n ∈ Icc 1 T with n < N₁, (3 + 31 * (N₁ : ℝ)) ^ 2 :=
          sum_le_sum hterm
      _ = (((Icc 1 T).filter (fun n => n < N₁)).card : ℝ) * (3 + 31 * N₁) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (N₁ : ℝ) * (3 + 31 * N₁) ^ 2 := by
          gcongr
          exact_mod_cast (card_le_card hsub).trans (card_range N₁).le
  -- large `n ≤ T`: the zero-free bound and the band
  have hlarge : ∑ n ∈ Icc 1 T with ¬ n < N₁, f n ≤ K ^ 2 * S := by
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n < N₁),
        f n ≤ K ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) := by
      intro n hn
      simp only [mem_filter, mem_Icc, not_lt] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hn0 : (0 : ℝ) < n := by linarith
      set ℓ := Real.log n with hℓ
      set u := Real.sqrt ℓ
      have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hn1
      have huu : u ^ 2 = ℓ := Real.sq_sqrt hℓ0
      have hu0 : 0 ≤ u := Real.sqrt_nonneg _
      have hA := hpre ε hε4 hε2 n hn.2
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (K * (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      -- the band: `2(1/2 - ε) ℓ ≤ u/40` for every `n ≤ T`
      have hbandn : (1 - 2 * ε) * ℓ ≤ u / 40 := by
        have huT : u ≤ Real.sqrt (Real.log T) := Real.sqrt_le_sqrt
          (Real.log_le_log hn0 (by exact_mod_cast hn.1.2))
        rcases (Real.sqrt_nonneg (Real.log T)).eq_or_lt with h0 | hpos
        · have hu00 : u = 0 := le_antisymm (h0 ▸ huT) hu0
          rw [← h0, mul_zero, div_zero] at hband
          rw [← huu, hu00]; nlinarith
        · have hb : 1 - 2 * ε ≤ 2 / (80 * Real.sqrt (Real.log T)) := by
            have : 2 / (80 * Real.sqrt (Real.log T)) = 2 * (1 / (80 * Real.sqrt (Real.log T))) := by
              ring
            rw [this]; linarith
          have hε' : 0 ≤ 1 - 2 * ε := by linarith
          calc (1 - 2 * ε) * ℓ = (1 - 2 * ε) * u * u := by rw [← huu]; ring
            _ ≤ 2 / (80 * Real.sqrt (Real.log T)) * u * u := by gcongr
            _ ≤ 2 / (80 * Real.sqrt (Real.log T)) * Real.sqrt (Real.log T) * u := by gcongr
            _ = u / 40 := by field_simp; ring
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-(u / 40)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          Real.exp (-(1 / 40 * u)) / n := by
        have hnpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = Real.exp (2 * ((1 - ε) * ℓ)) := by
          rw [Real.rpow_def_of_pos hn0, ← Real.exp_nat_mul, hℓ]; congr 1; push_cast; ring
        have hex : Real.exp (-(u / 40)) ^ 2 = Real.exp (-(u / 20)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        rw [hnpow, hex, ← Real.exp_add]
        rw [div_le_div_iff₀ (by positivity) hn0]
        have hnn : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
        have hnexp : (n : ℝ) = Real.exp ℓ := (Real.exp_log hn0).symm
        calc Real.exp (2 * ((1 - ε) * ℓ) + -(u / 20)) * n
            = Real.exp (-(1 / 40 * u)) * ((n : ℝ) * (n : ℝ)) *
                Real.exp ((1 - 2 * ε) * ℓ - u / 40) := by
              rw [hnexp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 1; ring
          _ ≤ Real.exp (-(1 / 40 * u)) * ((n : ℝ) * (n : ℝ)) * 1 := by
              gcongr
              exact Real.exp_le_one_iff.mpr (by linarith)
          _ ≤ Real.exp (-(1 / 40 * u)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hnn (Real.exp_pos _).le
      calc f n ≤ (K * (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hA2 (by positivity)
        _ = K ^ 2 * (((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-(u / 40)) ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) := by ring
        _ ≤ K ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg K)
    calc ∑ n ∈ Icc 1 T with ¬ n < N₁, f n
        ≤ ∑ n ∈ Icc 1 T with ¬ n < N₁, K ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) :=
          sum_le_sum hterm
      _ = K ^ 2 * ∑ n ∈ Icc 1 T with ¬ n < N₁,
            Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n := by rw [mul_sum]
      _ ≤ K ^ 2 * S := mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun m _ => by positivity) (sq_nonneg K)
  linarith

/-- **The Bézout interior energy on the zero-free band.** The same band bounds the interior energy,
`E^int_T(ε) ≤ 2 E_T(ε) + 1/2`. -/
theorem exists_interiorEnergy_le_on_zeroFreeBand :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        pmBezoutInteriorPronicEnergy ε T ≤ E := by
  obtain ⟨E, hE⟩ := exists_receiver_le_on_zeroFreeBand
  exact ⟨2 * E + 1 / 2, fun T ε h4 h2 hb =>
    (pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half (by linarith) T).trans
      (by linarith [hE T ε h4 h2 hb])⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
