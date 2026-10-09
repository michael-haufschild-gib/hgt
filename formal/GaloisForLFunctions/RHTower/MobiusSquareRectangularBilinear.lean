import GaloisForLFunctions.RHTower.MobiusSquareBilinearCutoff

set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction

namespace RHTower

private theorem rectangle_weighted_convolution
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

private theorem rectangle_zeta_convolution
    (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, (f * (g * (zeta : ArithmeticFunction ℝ))) n * w n) =
      ∑ a ∈ Icc 1 X, f a * ∑ b ∈ Icc 1 X,
        g b * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
  rw [rectangle_weighted_convolution]
  apply sum_congr rfl
  intro a ha
  congr 1
  rw [rectangle_weighted_convolution]
  have he : (∑ b ∈ Icc 1 (X / a), g b *
      ∑ k ∈ Icc 1 (X / a / b), (zeta : ArithmeticFunction ℝ) k * w (a * (b * k))) =
      ∑ b ∈ Icc 1 (X / a), g b * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
    apply sum_congr rfl
    intro b _
    congr 1
    rw [Nat.div_div_eq_div_mul]
    apply sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      if_neg hk0, Nat.cast_one, one_mul, Nat.mul_assoc]
  rw [he]
  apply sum_subset
  · intro b hb
    exact mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans (Nat.div_le_self X a)⟩
  · intro b hb hnot
    have ha0 : 0 < a := by have := (mem_Icc.mp ha).1; omega
    have hbcut : X / a < b := by
      have := (mem_Icc.mp hb).1
      simp only [mem_Icc] at hnot
      omega
    have hprod : X < a * b := by
      by_contra h
      have hle : b ≤ X / a := (Nat.le_div_iff_mul_le ha0).mpr (by nlinarith)
      omega
    simp [Nat.div_eq_of_lt hprod]

private theorem rectangle_low_sum {U X : ℕ} (hUX : U ≤ X) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 X, Sieve.truncatedMoebius U n * w n) =
      ∑ n ∈ Icc 1 U, (moebius n : ℝ) * w n := by
  have hs : Icc 1 U ⊆ Icc 1 X := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hUX⟩
  calc
    _ = ∑ n ∈ Icc 1 U, Sieve.truncatedMoebius U n * w n := by
      symm
      apply sum_subset hs
      intro n hn hnot
      have hnu : ¬ n ≤ U := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, h⟩)
      simp [hnu]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      simp [(mem_Icc.mp hn).2]

private theorem rectangle_tail_sum (U X : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 X, ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius U) n * w n) =
      ∑ n ∈ Ioc U X, (moebius n : ℝ) * w n := by
  have hs : Ioc U X ⊆ Icc 1 X := by
    intro n hn
    exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  calc
    _ = ∑ n ∈ Ioc U X, ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius U) n * w n := by
      symm
      apply sum_subset hs
      intro n hn hnot
      have hnu : n ≤ U := by
        have := (mem_Icc.mp hn).2
        simp only [mem_Ioc] at hnot
        omega
      change ((moebius n : ℝ) - Sieve.truncatedMoebius U n) * w n = 0
      simp [hnu]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      have hnu : ¬ n ≤ U := by have := (mem_Ioc.mp hn).1; omega
      change ((moebius n : ℝ) - Sieve.truncatedMoebius U n) * w n = (moebius n : ℝ) * w n
      simp [hnu]

/-- Exact asymmetric inversion, with both-large coefficients retained. -/
theorem sum_moebius_weight_eq_rectangular_with_tail
    {X U V : ℕ} (hU : U ≤ X) (hV : V ≤ X) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 X, (moebius n : ℝ) * w n) =
      (∑ n ∈ Icc 1 U, (moebius n : ℝ) * w n) +
      (∑ n ∈ Icc 1 V, (moebius n : ℝ) * w n) -
      (∑ a ∈ Icc 1 U, (moebius a : ℝ) * ∑ b ∈ Icc 1 V,
        (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k)) +
      ∑ a ∈ Ioc U X, (moebius a : ℝ) * ∑ b ∈ Ioc V X,
        (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
  let M := Sieve.truncatedMoebius U
  let L := Sieve.truncatedMoebius V
  let mu : ArithmeticFunction ℝ := moebius
  let Z : ArithmeticFunction ℝ := zeta
  have hmz : mu * Z = 1 := coe_moebius_mul_coe_zeta
  have halg : mu = M + L - M * (L * Z) + (mu - M) * ((mu - L) * Z) := by
    have hh : (mu - M) * ((mu - L) * Z) = mu - M - L + M * (L * Z) := by
      calc
        _ = mu * (mu * Z) - M * (mu * Z) - L * (mu * Z) + M * (L * Z) := by ring
        _ = _ := by rw [hmz]; simp
    rw [hh]
    ring
  have he : (∑ n ∈ Icc 1 X, (moebius n : ℝ) * w n) =
      (∑ n ∈ Icc 1 X, M n * w n) + (∑ n ∈ Icc 1 X, L n * w n) -
      (∑ n ∈ Icc 1 X, (M * (L * Z)) n * w n) +
      ∑ n ∈ Icc 1 X, ((mu - M) * ((mu - L) * Z)) n * w n := by
    rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) halg
    change (moebius n : ℝ) = M n + L n - (M * (L * Z)) n +
      ((mu - M) * ((mu - L) * Z)) n at hn
    rw [hn]
    ring
  have hlow : (∑ n ∈ Icc 1 X, (M * (L * Z)) n * w n) =
      ∑ a ∈ Icc 1 U, (moebius a : ℝ) * ∑ b ∈ Icc 1 V,
        (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
    dsimp only [M, L, Z]
    rw [rectangle_zeta_convolution, rectangle_low_sum hU]
    apply sum_congr rfl
    intro a _
    rw [rectangle_low_sum hV]
  have htail : (∑ n ∈ Icc 1 X, ((mu - M) * ((mu - L) * Z)) n * w n) =
      ∑ a ∈ Ioc U X, (moebius a : ℝ) * ∑ b ∈ Ioc V X,
        (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
    dsimp only [mu, M, L, Z]
    rw [rectangle_zeta_convolution, rectangle_tail_sum]
    apply sum_congr rfl
    intro a _
    rw [rectangle_tail_sum]
  rw [hlow, htail] at he
  dsimp only [M, L] at he
  rw [rectangle_low_sum hU, rectangle_low_sum hV] at he
  exact he

/-- A covering rectangle leaves no unrepresented product below `X`. -/
theorem sum_moebius_weight_eq_rectangular
    {X U V : ℕ} (hU : U ≤ X) (hV : V ≤ X)
    (hcover : X < (U + 1) * (V + 1)) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 X, (moebius n : ℝ) * w n) =
      (∑ n ∈ Icc 1 U, (moebius n : ℝ) * w n) +
      (∑ n ∈ Icc 1 V, (moebius n : ℝ) * w n) -
      ∑ a ∈ Icc 1 U, (moebius a : ℝ) * ∑ b ∈ Icc 1 V,
        (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
  rw [sum_moebius_weight_eq_rectangular_with_tail hU hV w]
  suffices hz : (∑ a ∈ Ioc U X, (moebius a : ℝ) * ∑ b ∈ Ioc V X,
      (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k)) = 0 by rw [hz, add_zero]
  apply sum_eq_zero
  intro a ha
  have hi : (∑ b ∈ Ioc V X, (moebius b : ℝ) *
      ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k)) = 0 := by
    apply sum_eq_zero
    intro b hb
    have hab : (U + 1) * (V + 1) ≤ a * b :=
      Nat.mul_le_mul (by have := (mem_Ioc.mp ha).1; omega)
        (by have := (mem_Ioc.mp hb).1; omega)
    simp [Nat.div_eq_of_lt (hcover.trans_le hab)]
  rw [hi, mul_zero]

noncomputable def logMobiusRectangularBilinearSquareAction (N U V : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, (moebius a : ℝ) *
    ∑ b ∈ Icc 1 V, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b)

/-- Retain both residue means when either factor cutoff exceeds `N`. -/
noncomputable def mobiusCenteredRectangularBilinearSquareSource (N U V : ℕ) : ℝ :=
  logMobiusRectangularBilinearSquareAction N U V -
    (1 + (∑ d ∈ Icc 1 U, (moebius d : ℝ) * Real.log d / d) +
      ∑ d ∈ Icc 1 V, (moebius d : ℝ) * Real.log d / d) *
      (∑ s ∈ range N, (s : ℝ) ^ 2) +
    (N : ℝ) / 2 * (∑ d ∈ Icc 1 U,
      ((moebius d : ℝ) * Real.log d) * (1 - 1 / (d : ℝ))) +
    (N : ℝ) / 2 * ∑ d ∈ Icc 1 V,
      ((moebius d : ℝ) * Real.log d) * (1 - 1 / (d : ℝ))

theorem logMobiusSquareFloorAction_eq_rectangular
    {N U V : ℕ} (hU : U ≤ N ^ 2) (hV : V ≤ N ^ 2)
    (hcover : N ^ 2 < (U + 1) * (V + 1)) :
    logMobiusSquareFloorAction N (N ^ 2) =
      logMobiusSquareFloorAction N U + logMobiusSquareFloorAction N V -
        logMobiusRectangularBilinearSquareAction N U V := by
  simpa only [logMobiusSquareFloorAction, logMobiusRectangularBilinearSquareAction,
    mobiusSquareShortBilinearKernel, mul_assoc] using
    sum_moebius_weight_eq_rectangular hU hV hcover
      (fun d => Real.log d * mobiusSquareFloorPrefix N d)

theorem psiRemainder_squareSum_eq_centered_rectangular
    {N U V : ℕ} (hN : 1 ≤ N) (hU : U ≤ N ^ 2) (hV : V ≤ N ^ 2)
    (hcover : N ^ 2 < (U + 1) * (V + 1)) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      mobiusCenteredRectangularBilinearSquareSource N U V +
        logMobiusCenteredQuadraticResidueAction N U +
        logMobiusCenteredQuadraticResidueAction N V := by
  rw [psiRemainder_squareSum_eq_logMobiusSquareFloor hN,
    logMobiusSquareFloorAction_eq_rectangular hU hV hcover,
    logMobiusSquareFloorAction_eq_harmonic_sub_residues,
    logMobiusSquareFloorAction_eq_harmonic_sub_residues]
  simp only [logMobiusQuadraticResidueAction,
    logMobiusQuadraticResidueAction_eq_mean_add_centered]
  unfold mobiusCenteredRectangularBilinearSquareSource
  ring

/-- An integral-power aperture condition covers both sublinear and superlinear cutoffs. -/
theorem abs_logMobiusCenteredQuadraticResidueAction_le_quartic_aperture
    {N D : ℕ} (hcritical : D ^ 4 ≤ N ^ 5) :
    |logMobiusCenteredQuadraticResidueAction N D| ≤
      4 * (41 : ℝ) ^ 4 * (N : ℝ) ^ 2 := by
  by_cases hDN : D ≤ N
  · have h := abs_logMobiusCenteredQuadraticResidueAction_le_mul hDN
    have hDN' : (D : ℝ) ≤ N := by exact_mod_cast hDN
    calc
      _ ≤ 16384 * (N : ℝ) * D := h
      _ ≤ 16384 * (N : ℝ) ^ 2 := by
        nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by norm_num : (16384 : ℝ) ≤ 4 * (41 : ℝ) ^ 4) (sq_nonneg (N : ℝ))
  · have hD : 1 ≤ D := by omega
    have hp : (D : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := by exact_mod_cast hcritical
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (D : ℝ) ^ 4) hp
      (by norm_num : (0 : ℝ) ≤ 2 / 5)
    have hd : ((D : ℝ) ^ 4) ^ (2 / 5 : ℝ) = (D : ℝ) ^ (8 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg D)]
      norm_num
    have hn : ((N : ℝ) ^ 5) ^ (2 / 5 : ℝ) = (N : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    rw [hd, hn] at hh
    have hh' : (D : ℝ) ^ (3 / 2 + (1 / 10 : ℝ)) ≤ (N : ℝ) ^ 2 := by
      norm_num
      exact hh
    have hb := abs_logMobiusCenteredQuadraticResidueAction_le_superlinear_aperture
      (by norm_num : (0 : ℝ) < 1 / 10) hD (by omega : N ≤ D) hh'
    convert hb using 1
    norm_num

/-- Unequal factors retain a critical error budget after both means are included. -/
theorem abs_psiRemainder_squareSum_sub_centered_rectangular_le
    {N U V : ℕ} (hN : 1 ≤ N) (hU : U ≤ N ^ 2) (hV : V ≤ N ^ 2)
    (hcover : N ^ 2 < (U + 1) * (V + 1))
    (hUpow : U ^ 4 ≤ N ^ 5) (hVpow : V ^ 4 ≤ N ^ 5) :
    |(∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) -
        mobiusCenteredRectangularBilinearSquareSource N U V| ≤
      8 * (41 : ℝ) ^ 4 * (N : ℝ) ^ 2 := by
  have he : (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) -
      mobiusCenteredRectangularBilinearSquareSource N U V =
      logMobiusCenteredQuadraticResidueAction N U +
        logMobiusCenteredQuadraticResidueAction N V := by
    rw [psiRemainder_squareSum_eq_centered_rectangular hN hU hV hcover]
    ring
  rw [he]
  calc
    _ ≤ |logMobiusCenteredQuadraticResidueAction N U| +
        |logMobiusCenteredQuadraticResidueAction N V| := abs_add_le _ _
    _ ≤ 4 * (41 : ℝ) ^ 4 * (N : ℝ) ^ 2 +
        4 * (41 : ℝ) ^ 4 * (N : ℝ) ^ 2 :=
      add_le_add (abs_logMobiusCenteredQuadraticResidueAction_le_quartic_aperture hUpow)
        (abs_logMobiusCenteredQuadraticResidueAction_le_quartic_aperture hVpow)
    _ = _ := by ring

/-- The signed rectangular upper bound is equivalent to RH; no cancellation premise is discharged. -/
theorem riemannHypothesis_iff_centeredRectangularBilinearSource_boundedAbove
    (U V : ℕ → ℕ)
    (hU : ∀ N : ℕ, 2 ≤ N → U N ≤ N ^ 2)
    (hV : ∀ N : ℕ, 2 ≤ N → V N ≤ N ^ 2)
    (hcover : ∀ N : ℕ, 2 ≤ N → N ^ 2 < (U N + 1) * (V N + 1))
    (hUpow : ∀ N : ℕ, 2 ≤ N → U N ^ 4 ≤ N ^ 5)
    (hVpow : ∀ N : ℕ, 2 ≤ N → V N ^ 4 ≤ N ^ 5) :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      mobiusCenteredRectangularBilinearSquareSource N (U N) (V N) ≤ B * (N : ℝ) ^ 2 := by
  rw [GaloisForLFunctions.RHTower.riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove]
  have herr (N : ℕ) (hN : 2 ≤ N) :=
    abs_psiRemainder_squareSum_sub_centered_rectangular_le
      (by omega : 1 ≤ N) (hU N hN) (hV N hN) (hcover N hN) (hUpow N hN) (hVpow N hN)
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + 8 * (41 : ℝ) ^ 4, ?_⟩
    intro N hN
    have hb := hB N hN
    have he := (abs_le.mp (herr N hN)).1
    nlinarith only [hb, he]
  · rintro ⟨B, hB⟩
    refine ⟨B + 8 * (41 : ℝ) ^ 4, ?_⟩
    intro N hN
    have hb := hB N hN
    have he := (abs_le.mp (herr N hN)).2
    nlinarith only [hb, he]

/-- Ceiling division gives a covering rectangle within the proved fourth-power budget. -/
theorem mobiusRectangularCutoffs_admissible {N t : ℕ}
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htpow : t ^ 4 ≤ N) :
    let U := (N - 1) / t + 1
    let V := N * t
    U ≤ N ∧ V ≤ N ^ 2 ∧ N ^ 2 < (U + 1) * (V + 1) ∧
      U ^ 4 ≤ N ^ 5 ∧ V ^ 4 ≤ N ^ 5 := by
  let U := (N - 1) / t + 1
  let V := N * t
  change U ≤ N ∧ V ≤ N ^ 2 ∧ N ^ 2 < (U + 1) * (V + 1) ∧
    U ^ 4 ≤ N ^ 5 ∧ V ^ 4 ≤ N ^ 5
  have hUN : U ≤ N := by
    dsimp only [U]
    have := Nat.div_le_self (N - 1) t
    omega
  have hUt : N ≤ U * t := by
    have hh : (N - 1) / t < U := by dsimp only [U]; omega
    have hh' : N - 1 < U * t := (Nat.div_lt_iff_lt_mul (by omega : 0 < t)).mp hh
    omega
  have ht2 : t ≤ t * t := by nlinarith
  have htN : t ≤ N := by
    calc
      t ≤ t * t := ht2
      _ ≤ (t * t) * (t * t) := Nat.mul_le_mul ht2 ht2
      _ = t ^ 4 := by ring
      _ ≤ N := htpow
  have hVN : V ≤ N ^ 2 := by
    dsimp only [V]
    simpa only [pow_two] using Nat.mul_le_mul_left N htN
  have hcover : N ^ 2 < (U + 1) * (V + 1) := by
    have hh := Nat.mul_le_mul_left N hUt
    dsimp only [V]
    nlinarith only [hh]
  have hNpow : N ^ 4 ≤ N ^ 5 := by
    calc
      N ^ 4 = N ^ 4 * 1 := by ring
      _ ≤ N ^ 4 * N := Nat.mul_le_mul_left _ hN
      _ = N ^ 5 := by ring
  have hUpow : U ^ 4 ≤ N ^ 5 := by
    have h2 := Nat.mul_le_mul hUN hUN
    have h4 := Nat.mul_le_mul h2 h2
    nlinarith only [h4, hNpow]
  have hVpow : V ^ 4 ≤ N ^ 5 := by
    dsimp only [V]
    calc
      (N * t) ^ 4 = N ^ 4 * t ^ 4 := by ring
      _ ≤ N ^ 4 * N := Nat.mul_le_mul_left _ htpow
      _ = N ^ 5 := by ring
  exact ⟨hUN, hVN, hcover, hUpow, hVpow⟩

/-- A concrete unequal-cutoff criterion, with no auxiliary aperture hypotheses. -/
theorem riemannHypothesis_iff_quarterRootRectangularBilinearSource_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      mobiusCenteredRectangularBilinearSquareSource N
        ((N - 1) / Nat.sqrt (Nat.sqrt N) + 1)
        (N * Nat.sqrt (Nat.sqrt N)) ≤ B * (N : ℝ) ^ 2 := by
  have hadm (N : ℕ) (hN : 2 ≤ N) :
      let U := (N - 1) / Nat.sqrt (Nat.sqrt N) + 1
      let V := N * Nat.sqrt (Nat.sqrt N)
      U ≤ N ∧ V ≤ N ^ 2 ∧ N ^ 2 < (U + 1) * (V + 1) ∧
        U ^ 4 ≤ N ^ 5 ∧ V ^ 4 ≤ N ^ 5 := by
    have ht : 1 ≤ Nat.sqrt (Nat.sqrt N) :=
      Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr (by omega : 0 < N))
    have ht4 : Nat.sqrt (Nat.sqrt N) ^ 4 ≤ N := by
      have hh := Nat.sqrt_le (Nat.sqrt N)
      calc
        Nat.sqrt (Nat.sqrt N) ^ 4 =
            (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) *
              (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) := by ring
        _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul hh hh
        _ ≤ N := Nat.sqrt_le N
    exact mobiusRectangularCutoffs_admissible (by omega) ht ht4
  apply riemannHypothesis_iff_centeredRectangularBilinearSource_boundedAbove
    (fun N => (N - 1) / Nat.sqrt (Nat.sqrt N) + 1)
    (fun N => N * Nat.sqrt (Nat.sqrt N))
  · intro N hN
    have hh := (hadm N hN).1
    nlinarith
  · intro N hN
    exact (hadm N hN).2.1
  · intro N hN
    exact (hadm N hN).2.2.1
  · intro N hN
    exact (hadm N hN).2.2.2.1
  · intro N hN
    exact (hadm N hN).2.2.2.2

end RHTower
