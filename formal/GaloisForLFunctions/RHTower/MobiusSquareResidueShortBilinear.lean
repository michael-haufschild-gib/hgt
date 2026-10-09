import GaloisForLFunctions.RHTower.MobiusSquareResidueSmallModuli
import GaloisForLFunctions.RHTower.LogarithmicMobiusShortReconstruction
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# Signed short bilinear reconstruction of the square-sampled source

The exact short Möbius inverse replaces coefficients up to N² by two
independent factors at most N, retaining the logarithmic weight and every
product cutoff. The resulting bilinear source differs from the actual
square-sampled Chebyshev remainder by twice the already-bounded small-modulus
residue action. Its one-sided quadratic bound is therefore equivalent to RH.

The kernel is nonnegative with an exact support threshold. Its positive
diagonal has a cubic lower bound, while its principal minor at indices 1 and N
is negative for every N ≥ 3. The signed off-diagonal contribution remains essential.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction

namespace RHTower

private theorem square_short_weighted_convolution
    (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, (f * g) n * w n) =
      ∑ a ∈ Icc 1 X, f a * ∑ b ∈ Icc 1 (X / a), g b * w (a * b) := by
  have he : (∑ n ∈ Icc 1 X, (f * g) n * w n) =
      ∑ n ∈ Icc 1 X, ∑ x ∈ n.divisorsAntidiagonal,
        f x.1 * g x.2 * w (x.1 * x.2) := by
    apply sum_congr rfl
    intro n _
    rw [ArithmeticFunction.mul_apply, sum_mul]
    apply sum_congr rfl
    intro x hx
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [he, Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun a b => f a * g b * w (a * b)) X]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

private theorem square_short_truncated_sum {U X : ℕ} (hU : U ≤ X) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 X, Sieve.truncatedMoebius U n * w n) =
      ∑ n ∈ Icc 1 U, (moebius n : ℝ) * w n := by
  have hs : Icc 1 U ⊆ Icc 1 X := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hU⟩
  calc
    _ = ∑ n ∈ Icc 1 U, Sieve.truncatedMoebius U n * w n := by
      symm
      apply sum_subset hs
      intro n hn hnU
      have hn' : ¬n ≤ U := fun h => hnU (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, h⟩)
      simp only [Sieve.truncatedMoebius_apply, if_neg hn', zero_mul]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [Sieve.truncatedMoebius_apply, if_pos (mem_Icc.mp hn).2]

private theorem square_short_correction_rectangle (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 (N ^ 2),
      (Sieve.truncatedMoebius N *
        (Sieve.truncatedMoebius N * (zeta : ArithmeticFunction ℝ))) n * w n) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (moebius a : ℝ) * (moebius b : ℝ) *
          ∑ k ∈ Icc 1 (N ^ 2 / (a * b)), w (a * b * k) := by
  have hNN : N ≤ N ^ 2 := by
    by_cases hN : N = 0
    · simp [hN]
    · have hn : 1 ≤ N := by omega
      simpa [pow_two] using Nat.mul_le_mul_left N hn
  rw [square_short_weighted_convolution, square_short_truncated_sum hNN]
  apply sum_congr rfl
  intro a ha
  have ha' := mem_Icc.mp ha
  have hinner : N ≤ N ^ 2 / a := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < a)]
    simpa [pow_two] using Nat.mul_le_mul_left N ha'.2
  rw [square_short_weighted_convolution, square_short_truncated_sum hinner, mul_sum]
  apply sum_congr rfl
  intro b _
  rw [Nat.div_div_eq_div_mul, mul_assoc]
  apply congrArg (fun t : ℝ => (moebius a : ℝ) * ((moebius b : ℝ) * t))
  apply sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg hk0, Nat.cast_one, one_mul, Nat.mul_assoc]

/-- Exact finite signed reconstruction using two independent short Möbius factors. -/
theorem sum_moebius_weight_eq_short_bilinear (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 (N ^ 2), (moebius n : ℝ) * w n) =
      2 * (∑ n ∈ Icc 1 N, (moebius n : ℝ) * w n) -
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (moebius a : ℝ) * (moebius b : ℝ) *
          ∑ k ∈ Icc 1 (N ^ 2 / (a * b)), w (a * b * k) := by
  have hNN : N ≤ N ^ 2 := by
    by_cases hN : N = 0
    · simp [hN]
    · have hn : 1 ≤ N := by omega
      simpa [pow_two] using Nat.mul_le_mul_left N hn
  have he : (∑ n ∈ Icc 1 (N ^ 2), (moebius n : ℝ) * w n) =
      2 * (∑ n ∈ Icc 1 (N ^ 2), Sieve.truncatedMoebius N n * w n) -
      ∑ n ∈ Icc 1 (N ^ 2),
        (Sieve.truncatedMoebius N *
          (Sieve.truncatedMoebius N * (zeta : ArithmeticFunction ℝ))) n * w n := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    rw [moebius_eq_short_square_correction N n
      (by have := (mem_Icc.mp hn).2; nlinarith)]
    ring
  rw [he, square_short_truncated_sum hNN, square_short_correction_rectangle]

noncomputable def mobiusSquareFloorPrefix (N d : ℕ) : ℝ :=
  ∑ s ∈ range N, ((s ^ 2 / d : ℕ) : ℝ)

noncomputable def logMobiusSquareFloorAction (N D : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 D, (moebius d : ℝ) * Real.log d * mobiusSquareFloorPrefix N d

theorem quadraticResiduePrefix_add_mul_floor (N d : ℕ) :
    quadraticResiduePrefix N d + (d : ℝ) * mobiusSquareFloorPrefix N d =
      ∑ s ∈ range N, (s : ℝ) ^ 2 := by
  unfold quadraticResiduePrefix mobiusSquareFloorPrefix
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro s _
  exact_mod_cast Nat.mod_add_div (s ^ 2) d

theorem logMobiusSquareFloorAction_eq_harmonic_sub_residues (N D : ℕ) :
    logMobiusSquareFloorAction N D =
      (∑ d ∈ Icc 1 D, (moebius d : ℝ) * Real.log d / d) *
        (∑ s ∈ range N, (s : ℝ) ^ 2) - logMobiusQuadraticResidueAction N D := by
  have hterm (d : ℕ) (hd : d ∈ Icc 1 D) :
      (moebius d : ℝ) * Real.log d * mobiusSquareFloorPrefix N d =
        ((moebius d : ℝ) * Real.log d / d) * (∑ s ∈ range N, (s : ℝ) ^ 2) -
        ((moebius d : ℝ) * Real.log d / d) * quadraticResiduePrefix N d := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hv := quadraticResiduePrefix_add_mul_floor N d
    have hf : (d : ℝ) * mobiusSquareFloorPrefix N d =
        (∑ s ∈ range N, (s : ℝ) ^ 2) - quadraticResiduePrefix N d := by linarith
    calc
      _ = ((moebius d : ℝ) * Real.log d / d) *
          ((d : ℝ) * mobiusSquareFloorPrefix N d) := by field_simp [ne_of_gt hdpos]
      _ = _ := by rw [hf]; ring
  unfold logMobiusSquareFloorAction logMobiusQuadraticResidueAction
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul]

theorem psiRemainder_squareSum_eq_logMobiusSquareFloor {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      -logMobiusSquareFloorAction N (N ^ 2) - ∑ s ∈ range N, (s : ℝ) ^ 2 := by
  rw [psiRemainder_squareSum_eq_quadraticResidues hN,
    logMobiusSquareFloorAction_eq_harmonic_sub_residues]
  unfold logMobiusQuadraticResidueAction
  ring

noncomputable def mobiusSquareShortBilinearKernel (N q : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (N ^ 2 / q), Real.log (q * k : ℕ) * mobiusSquareFloorPrefix N (q * k)

noncomputable def logMobiusShortBilinearSquareAction (N : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
    (moebius a : ℝ) * (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b)

noncomputable def mobiusShortBilinearSquareSource (N : ℕ) : ℝ :=
  logMobiusShortBilinearSquareAction N -
    (1 + 2 * ∑ d ∈ Icc 1 N, (moebius d : ℝ) * Real.log d / d) *
      ∑ s ∈ range N, (s : ℝ) ^ 2

theorem logMobiusSquareFloorAction_eq_short_bilinear (N : ℕ) :
    logMobiusSquareFloorAction N (N ^ 2) =
      2 * logMobiusSquareFloorAction N N - logMobiusShortBilinearSquareAction N := by
  simpa only [logMobiusSquareFloorAction, logMobiusShortBilinearSquareAction,
    mobiusSquareShortBilinearKernel, mul_assoc] using
    sum_moebius_weight_eq_short_bilinear N (fun n => Real.log n * mobiusSquareFloorPrefix N n)

/-- All long Möbius coefficients are replaced by a signed short rectangle and a critical error. -/
theorem psiRemainder_squareSum_eq_shortBilinearSource {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      mobiusShortBilinearSquareSource N + 2 * logMobiusQuadraticResidueAction N N := by
  rw [psiRemainder_squareSum_eq_logMobiusSquareFloor hN,
    logMobiusSquareFloorAction_eq_short_bilinear,
    logMobiusSquareFloorAction_eq_harmonic_sub_residues]
  unfold mobiusShortBilinearSquareSource
  ring

theorem exists_abs_psiRemainder_squareSum_sub_shortBilinearSource_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) - mobiusShortBilinearSquareSource N| ≤
        C * (N : ℝ) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_logMobiusQuadraticResidueAction_self_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  have he : (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) - mobiusShortBilinearSquareSource N =
      2 * logMobiusQuadraticResidueAction N N := by
    rw [psiRemainder_squareSum_eq_shortBilinearSource hN]
    ring
  calc
    _ = 2 * |logMobiusQuadraticResidueAction N N| := by rw [he, abs_mul]; norm_num
    _ ≤ 2 * (C * (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

theorem riemannHypothesis_iff_mobiusShortBilinearSquareSource_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      mobiusShortBilinearSquareSource N ≤ B * (N : ℝ) ^ 2 := by
  rw [GaloisForLFunctions.RHTower.riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove]
  obtain ⟨C, _, hC⟩ := exists_abs_psiRemainder_squareSum_sub_shortBilinearSource_le
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + C, ?_⟩
    intro N hN
    have hb := hB N hN
    have hc := (abs_le.mp (hC N (by omega))).1
    nlinarith only [hb, hc]
  · rintro ⟨B, hB⟩
    refine ⟨B + C, ?_⟩
    intro N hN
    have hb := hB N hN
    have hc := (abs_le.mp (hC N (by omega))).2
    nlinarith only [hb, hc]

theorem mobiusSquareShortBilinearKernel_nonneg (N q : ℕ) :
    0 ≤ mobiusSquareShortBilinearKernel N q := by
  apply sum_nonneg
  intro k _
  apply mul_nonneg (Real.log_natCast_nonneg (q * k))
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

noncomputable def logMobiusShortBilinearSquareDiagonal (N : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * mobiusSquareShortBilinearKernel N (a ^ 2)

noncomputable def logMobiusShortBilinearSquareOffDiagonal (N : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ (Icc 1 N).erase a,
    (moebius a : ℝ) * (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b)

theorem logMobiusShortBilinearSquareAction_eq_diagonal_add_offDiagonal (N : ℕ) :
    logMobiusShortBilinearSquareAction N =
      logMobiusShortBilinearSquareDiagonal N + logMobiusShortBilinearSquareOffDiagonal N := by
  unfold logMobiusShortBilinearSquareAction logMobiusShortBilinearSquareDiagonal
    logMobiusShortBilinearSquareOffDiagonal
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  simp only [pow_two]
  have h := sum_erase_add (s := Icc 1 N)
    (f := fun b => (moebius a : ℝ) * (moebius b : ℝ) *
      mobiusSquareShortBilinearKernel N (a * b)) ha
  linarith only [h]

private theorem square_short_six_mul_moment (N : ℕ) :
    6 * (∑ s ∈ range N, (s : ℝ) ^ 2) = (N : ℝ) * ((N : ℝ) - 1) * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith only [ih]

private theorem square_short_floor_two_lower {N : ℕ} (hN : 4 ≤ N) :
    (N : ℝ) ^ 3 / 32 ≤ mobiusSquareFloorPrefix N 2 := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hmoment := square_short_six_mul_moment N
  have hfac : 0 ≤ (N : ℝ) * ((N : ℝ) - 2) * (5 * N - 2) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (by linarith)) (by linarith)
  have hQ : (N : ℝ) ^ 3 / 8 ≤ ∑ s ∈ range N, (s : ℝ) ^ 2 := by
    nlinarith only [hmoment, hfac]
  have hV : quadraticResiduePrefix N 2 ≤ (N : ℝ) := by
    unfold quadraticResiduePrefix
    calc
      _ ≤ ∑ _s ∈ range N, (1 : ℝ) := by
        apply sum_le_sum
        intro s _
        have hm : s ^ 2 % 2 ≤ 1 := by have := Nat.mod_lt (s ^ 2) (by omega : 0 < 2); omega
        exact_mod_cast hm
      _ = _ := by simp
  have hdiv := quadraticResiduePrefix_add_mul_floor N 2
  have hcube : 0 ≤ (N : ℝ) * ((N : ℝ) - 4) * ((N : ℝ) + 4) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (by linarith)) (by positivity)
  norm_num only [Nat.cast_ofNat] at hdiv
  nlinarith only [hQ, hV, hdiv, hcube]

/-- The actual positive diagonal has a cubic lower bound. -/
theorem logMobiusShortBilinearSquareDiagonal_cubic_lower {N : ℕ} (hN : 4 ≤ N) :
    Real.log 2 / 32 * (N : ℝ) ^ 3 ≤ logMobiusShortBilinearSquareDiagonal N := by
  have hk : ({2} : Finset ℕ) ⊆ Icc 1 (N ^ 2 / 1) := by
    intro k hk
    have hk2 : k = 2 := mem_singleton.mp hk
    subst k
    simp only [Nat.div_one, mem_Icc]
    constructor <;> nlinarith
  have hkbound := sum_le_sum_of_subset_of_nonneg hk
    (f := fun k => Real.log (1 * k : ℕ) * mobiusSquareFloorPrefix N (1 * k))
    (fun k _ _ => mul_nonneg (Real.log_natCast_nonneg (1 * k))
      (sum_nonneg fun _ _ => Nat.cast_nonneg _))
  have hkernel : Real.log 2 * mobiusSquareFloorPrefix N 2 ≤ mobiusSquareShortBilinearKernel N 1 := by
    simpa [mobiusSquareShortBilinearKernel] using hkbound
  have ha : ({1} : Finset ℕ) ⊆ Icc 1 N := by
    intro a ha
    have ha1 : a = 1 := mem_singleton.mp ha
    subst a
    simp only [mem_Icc]
    omega
  have hdiag := sum_le_sum_of_subset_of_nonneg ha
    (f := fun a => (moebius a : ℝ) ^ 2 * mobiusSquareShortBilinearKernel N (a ^ 2))
    (fun a _ _ => mul_nonneg (sq_nonneg _) (mobiusSquareShortBilinearKernel_nonneg N _))
  have hkernel_diag : mobiusSquareShortBilinearKernel N 1 ≤ logMobiusShortBilinearSquareDiagonal N := by
    simpa [logMobiusShortBilinearSquareDiagonal] using hdiag
  calc
    _ = Real.log 2 * ((N : ℝ) ^ 3 / 32) := by ring
    _ ≤ Real.log 2 * mobiusSquareFloorPrefix N 2 :=
      mul_le_mul_of_nonneg_left (square_short_floor_two_lower hN) (Real.log_nonneg (by norm_num))
    _ ≤ _ := hkernel.trans hkernel_diag

/-- A modulus above the largest sampled square has exactly zero response. -/
theorem mobiusSquareShortBilinearKernel_eq_zero_of_cutoff {N q : ℕ}
    (hcut : (N - 1) ^ 2 < q) : mobiusSquareShortBilinearKernel N q = 0 := by
  apply sum_eq_zero
  intro k hk
  have hqk : q ≤ q * k := Nat.le_mul_of_pos_right q (by have := (mem_Icc.mp hk).1; omega)
  have hF : mobiusSquareFloorPrefix N (q * k) = 0 := by
    apply sum_eq_zero
    intro s hs
    have hs' : s ≤ N - 1 := by have := mem_range.mp hs; omega
    have hsq : s ^ 2 ≤ (N - 1) ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hs' hs'
    have hsmall : s ^ 2 < q * k := hsq.trans_lt (hcut.trans_le hqk)
    simp only [Nat.div_eq_of_lt hsmall, Nat.cast_zero]
  rw [hF, mul_zero]

private theorem square_short_kernel_pos {N q : ℕ} (hN : 1 ≤ N) (hq : 2 ≤ q)
    (hcut : q ≤ (N - 1) ^ 2) : 0 < mobiusSquareShortBilinearKernel N q := by
  have hq0 : 0 < q := by omega
  have hs : ({N - 1} : Finset ℕ) ⊆ range N := by
    intro s hs
    rw [mem_singleton] at hs
    subst s
    exact mem_range.mpr (by omega)
  have hsum := sum_le_sum_of_subset_of_nonneg hs
    (f := fun s => ((s ^ 2 / q : ℕ) : ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
  have hsingle : (((N - 1) ^ 2 / q : ℕ) : ℝ) ≤ mobiusSquareFloorPrefix N q := by
    simpa [mobiusSquareFloorPrefix] using hsum
  have hdiv : 1 ≤ (N - 1) ^ 2 / q :=
    (Nat.le_div_iff_mul_le hq0).mpr (by simpa using hcut)
  have hdivR : (1 : ℝ) ≤ (((N - 1) ^ 2 / q : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hF : (1 : ℝ) ≤ mobiusSquareFloorPrefix N q := hdivR.trans hsingle
  have hsub : N - 1 ≤ N := by omega
  have hqN : q ≤ N ^ 2 := hcut.trans (by
    simpa only [pow_two] using Nat.mul_le_mul hsub hsub)
  have hk : ({1} : Finset ℕ) ⊆ Icc 1 (N ^ 2 / q) := by
    intro k hk
    have hk1 : k = 1 := mem_singleton.mp hk
    subst k
    exact mem_Icc.mpr ⟨le_rfl, (Nat.le_div_iff_mul_le hq0).mpr (by simpa using hqN)⟩
  have hksum := sum_le_sum_of_subset_of_nonneg hk
    (f := fun k => Real.log (q * k : ℕ) * mobiusSquareFloorPrefix N (q * k))
    (fun k _ _ => mul_nonneg (Real.log_natCast_nonneg (q * k))
      (sum_nonneg fun _ _ => Nat.cast_nonneg _))
  have hK : Real.log q * mobiusSquareFloorPrefix N q ≤ mobiusSquareShortBilinearKernel N q := by
    simpa [mobiusSquareShortBilinearKernel] using hksum
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  exact (mul_pos hlog (by linarith : 0 < mobiusSquareFloorPrefix N q)).trans_le hK

/-- Away from modulus one, the kernel's positivity threshold is the largest sampled square. -/
theorem mobiusSquareShortBilinearKernel_pos_iff {N q : ℕ} (hN : 1 ≤ N) (hq : 2 ≤ q) :
    0 < mobiusSquareShortBilinearKernel N q ↔ q ≤ (N - 1) ^ 2 := by
  constructor
  · intro hpos
    by_contra h
    have hz := mobiusSquareShortBilinearKernel_eq_zero_of_cutoff (lt_of_not_ge h)
    rw [hz] at hpos
    linarith
  · exact square_short_kernel_pos hN hq

theorem mobiusSquareShortBilinearKernel_terminal_zero (N : ℕ) :
    mobiusSquareShortBilinearKernel N (N ^ 2) = 0 := by
  by_cases hN : N = 0
  · simp [hN, mobiusSquareShortBilinearKernel]
  apply mobiusSquareShortBilinearKernel_eq_zero_of_cutoff
  have hp : N - 1 + 1 = N := by omega
  have he : (N - 1) ^ 2 + 2 * (N - 1) + 1 = N ^ 2 := by
    calc
      _ = (N - 1 + 1) ^ 2 := by ring
      _ = _ := by rw [hp]
  omega

/-- The two-coordinate kernel at indices 1 and N has a negative principal minor for every N ≥ 3. -/
theorem mobiusSquareShortBilinearKernel_terminal_minor_neg {N : ℕ} (hN : 3 ≤ N) :
    mobiusSquareShortBilinearKernel N 1 * mobiusSquareShortBilinearKernel N (N ^ 2) -
      (mobiusSquareShortBilinearKernel N N) ^ 2 < 0 := by
  have hp : N - 1 + 1 = N := by omega
  have hm := Nat.mul_le_mul_left (N - 1) (show 2 ≤ N - 1 by omega)
  have hcut : N ≤ (N - 1) ^ 2 := by
    have hp1 : 1 ≤ N - 1 := by omega
    nlinarith only [hp, hm, hp1]
  have hpos : 0 < mobiusSquareShortBilinearKernel N N :=
    (mobiusSquareShortBilinearKernel_pos_iff (by omega) (by omega)).mpr hcut
  have hsq : 0 < (mobiusSquareShortBilinearKernel N N) ^ 2 := by
    simpa only [pow_two] using mul_pos hpos hpos
  rw [mobiusSquareShortBilinearKernel_terminal_zero, mul_zero]
  linarith

end RHTower
