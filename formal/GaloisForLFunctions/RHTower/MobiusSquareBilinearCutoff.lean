import GaloisForLFunctions.RHTower.MobiusSquareResidueShortBilinear

/-!
# Shortening the signed bilinear square source

An arbitrary coefficient cutoff leaves exactly the rectangle of two omitted
Möbius factors. For U = N - H with 4H ≤ N, its absolute contribution is at most
18 H³ log N. A uniform bound on the entire small-modulus residue action then
shows that cutoffs with H³ log N = O(N²) preserve the one-sided RH criterion.
The retained shorter signed rectangle is not bounded here.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction

namespace RHTower

private theorem square_cutoff_weighted_convolution
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

private theorem square_cutoff_rectangle
    (f : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, (f * (f * (zeta : ArithmeticFunction ℝ))) n * w n) =
      ∑ a ∈ Icc 1 X, f a * ∑ b ∈ Icc 1 X,
        f b * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
  rw [square_cutoff_weighted_convolution]
  apply sum_congr rfl
  intro a ha
  congr 1
  rw [square_cutoff_weighted_convolution]
  have he : (∑ b ∈ Icc 1 (X / a), f b *
      ∑ k ∈ Icc 1 (X / a / b), (zeta : ArithmeticFunction ℝ) k * w (a * (b * k))) =
      ∑ b ∈ Icc 1 (X / a), f b * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
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

private theorem square_cutoff_low_sum {U X : ℕ} (hUX : U ≤ X) (w : ℕ → ℝ) :
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

private theorem square_cutoff_tail_sum (U X : ℕ) (w : ℕ → ℝ) :
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

noncomputable def logMobiusCutoffBilinearSquareAction (N U : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, (moebius a : ℝ) *
    ∑ b ∈ Icc 1 U, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b)

noncomputable def logMobiusTailBilinearSquareAction (N U : ℕ) : ℝ :=
  ∑ a ∈ Ioc U (N ^ 2), (moebius a : ℝ) *
    ∑ b ∈ Ioc U (N ^ 2), (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b)

noncomputable def mobiusCutoffBilinearSquareSource (N U : ℕ) : ℝ :=
  logMobiusCutoffBilinearSquareAction N U -
    (1 + 2 * ∑ d ∈ Icc 1 U, (moebius d : ℝ) * Real.log d / d) *
      ∑ s ∈ range N, (s : ℝ) ^ 2

/-- An arbitrary coefficient cutoff leaves exactly the rectangle of two omitted factors. -/
theorem logMobiusSquareFloorAction_eq_cutoff_bilinear {N U : ℕ} (hU : U ≤ N ^ 2) :
    logMobiusSquareFloorAction N (N ^ 2) =
      2 * logMobiusSquareFloorAction N U - logMobiusCutoffBilinearSquareAction N U +
        logMobiusTailBilinearSquareAction N U := by
  let M := Sieve.truncatedMoebius U
  let mu : ArithmeticFunction ℝ := moebius
  let Z : ArithmeticFunction ℝ := zeta
  have hmz : mu * Z = 1 := coe_moebius_mul_coe_zeta
  have halg : mu = M + M - M * (M * Z) + (mu - M) * ((mu - M) * Z) := by
    have hh : (mu - M) * ((mu - M) * Z) = mu - M - M + M * (M * Z) := by
      calc
        _ = mu * (mu * Z) - M * (mu * Z) - M * (mu * Z) + M * (M * Z) := by ring
        _ = _ := by rw [hmz]; simp
    rw [hh]
    ring
  let w : ℕ → ℝ := fun n => Real.log n * mobiusSquareFloorPrefix N n
  have he : (∑ n ∈ Icc 1 (N ^ 2), (moebius n : ℝ) * w n) =
      2 * (∑ n ∈ Icc 1 (N ^ 2), M n * w n) -
        (∑ n ∈ Icc 1 (N ^ 2), (M * (M * Z)) n * w n) +
        ∑ n ∈ Icc 1 (N ^ 2), ((mu - M) * ((mu - M) * Z)) n * w n := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) halg
    change (moebius n : ℝ) = M n + M n - (M * (M * Z)) n +
      ((mu - M) * ((mu - M) * Z)) n at hn
    rw [hn]
    ring
  have hlow : (∑ n ∈ Icc 1 (N ^ 2), (M * (M * Z)) n * w n) =
      logMobiusCutoffBilinearSquareAction N U := by
    dsimp only [M, Z]
    rw [square_cutoff_rectangle, square_cutoff_low_sum hU]
    unfold logMobiusCutoffBilinearSquareAction
    apply sum_congr rfl
    intro a _
    rw [square_cutoff_low_sum hU]
    rfl
  have htail : (∑ n ∈ Icc 1 (N ^ 2), ((mu - M) * ((mu - M) * Z)) n * w n) =
      logMobiusTailBilinearSquareAction N U := by
    dsimp only [mu, M, Z]
    rw [square_cutoff_rectangle, square_cutoff_tail_sum]
    unfold logMobiusTailBilinearSquareAction
    apply sum_congr rfl
    intro a _
    rw [square_cutoff_tail_sum]
    rfl
  rw [hlow, htail] at he
  dsimp only [M] at he
  rw [square_cutoff_low_sum hU] at he
  simpa only [logMobiusSquareFloorAction, w, mul_assoc] using he

theorem psiRemainder_squareSum_eq_cutoff_bilinear {N U : ℕ}
    (hN : 1 ≤ N) (hU : U ≤ N ^ 2) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      mobiusCutoffBilinearSquareSource N U + 2 * logMobiusQuadraticResidueAction N U -
        logMobiusTailBilinearSquareAction N U := by
  rw [psiRemainder_squareSum_eq_logMobiusSquareFloor hN,
    logMobiusSquareFloorAction_eq_cutoff_bilinear hU,
    logMobiusSquareFloorAction_eq_harmonic_sub_residues]
  unfold mobiusCutoffBilinearSquareSource
  ring

/-- Above U squared, at most N-U sampled floors survive in the near-boundary regime. -/
theorem mobiusSquareFloorPrefix_le_boundary {N U q : ℕ}
    (_hUN : U ≤ N) (hq : U ^ 2 < q) (hclose : N ^ 2 < 2 * q) :
    mobiusSquareFloorPrefix N q ≤ ((N - U : ℕ) : ℝ) := by
  have hq0 : 0 < q := by omega
  have hs : Ico U N ⊆ range N := fun s hs => mem_range.mpr (mem_Ico.mp hs).2
  have he : mobiusSquareFloorPrefix N q =
      ∑ s ∈ Ico U N, ((s ^ 2 / q : ℕ) : ℝ) := by
    symm
    apply sum_subset hs
    intro s hs hnot
    have hsU : s ≤ U := by
      have := mem_range.mp hs
      simp only [mem_Ico] at hnot
      omega
    have hsq : s ^ 2 ≤ U ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hsU hsU
    simp [Nat.div_eq_of_lt (hsq.trans_lt hq)]
  rw [he]
  calc
    _ ≤ ∑ _s ∈ Ico U N, (1 : ℝ) := by
      apply sum_le_sum
      intro s hs
      have hsN : s ≤ N := (mem_Ico.mp hs).2.le
      have hsq : s ^ 2 ≤ N ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hsN hsN
      have hd : s ^ 2 / q < 2 := (Nat.div_lt_iff_lt_mul hq0).mpr (by nlinarith)
      exact_mod_cast (show s ^ 2 / q ≤ 1 by omega)
    _ = _ := by simp

theorem mobiusSquareShortBilinearKernel_le_boundary {N U q : ℕ}
    (hUN : U ≤ N) (hq : U ^ 2 < q) (hclose : N ^ 2 < 2 * q) :
    mobiusSquareShortBilinearKernel N q ≤
      2 * ((N - U : ℕ) : ℝ) * Real.log N := by
  have hlogN := Real.log_natCast_nonneg N
  by_cases hqN : q ≤ N ^ 2
  · have hq0 : 0 < q := by omega
    have hlo : 1 ≤ N ^ 2 / q := (Nat.le_div_iff_mul_le hq0).mpr (by simpa using hqN)
    have hhi : N ^ 2 / q < 2 := (Nat.div_lt_iff_lt_mul hq0).mpr (by nlinarith)
    have hd : N ^ 2 / q = 1 := by omega
    have hlog : Real.log (q : ℝ) ≤ 2 * Real.log N := by
      calc
        _ ≤ Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log (by exact_mod_cast hq0) (by exact_mod_cast hqN)
        _ = _ := by rw [Real.log_pow]; ring
    have hF := mobiusSquareFloorPrefix_le_boundary hUN hq hclose
    have hF0 : 0 ≤ mobiusSquareFloorPrefix N q := sum_nonneg fun _ _ => Nat.cast_nonneg _
    simp only [mobiusSquareShortBilinearKernel, hd, Icc_self, sum_singleton, Nat.mul_one]
    calc
      _ ≤ (2 * Real.log N) * ((N - U : ℕ) : ℝ) :=
        mul_le_mul hlog hF hF0 (by positivity)
      _ = _ := by ring
  · have hd : N ^ 2 / q = 0 := Nat.div_eq_of_lt (by omega)
    simp only [mobiusSquareShortBilinearKernel, hd]
    simp only [show Icc (1 : ℕ) 0 = ∅ from by decide, sum_empty]
    positivity

private theorem square_cutoff_tail_restrict {N U B : ℕ}
    (_hUB : U ≤ B) (hB : B ≤ N ^ 2) (hcap : N ^ 2 ≤ (U + 1) * B) :
    logMobiusTailBilinearSquareAction N U =
      ∑ a ∈ Ioc U B, (moebius a : ℝ) *
        ∑ b ∈ Ioc U B, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b) := by
  have hs : Ioc U B ⊆ Ioc U (N ^ 2) := fun a ha =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp ha).1, (mem_Ioc.mp ha).2.trans hB⟩
  have hz (a b : ℕ) (ha : B < a) (hb : U < b) :
      mobiusSquareShortBilinearKernel N (a * b) = 0 := by
    have hUp : 0 < U + 1 := by omega
    have hh : (U + 1) * B < (U + 1) * a := Nat.mul_lt_mul_of_pos_left ha hUp
    have hab : (U + 1) * a ≤ b * a := Nat.mul_le_mul_right a (by omega)
    have hprod : N ^ 2 < a * b := by nlinarith
    simp [mobiusSquareShortBilinearKernel, Nat.div_eq_of_lt hprod]
  unfold logMobiusTailBilinearSquareAction
  calc
    _ = ∑ a ∈ Ioc U B, (moebius a : ℝ) *
        ∑ b ∈ Ioc U (N ^ 2), (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b) := by
      symm
      apply sum_subset hs
      intro a ha hnot
      have haB : B < a := by
        have := (mem_Ioc.mp ha).1
        simp only [mem_Ioc] at hnot
        omega
      have he : (∑ b ∈ Ioc U (N ^ 2), (moebius b : ℝ) *
          mobiusSquareShortBilinearKernel N (a * b)) = 0 := by
        apply sum_eq_zero
        intro b hb
        rw [hz a b haB (mem_Ioc.mp hb).1, mul_zero]
      rw [he, mul_zero]
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      congr 1
      symm
      apply sum_subset hs
      intro b hb hnot
      have hbB : B < b := by
        have := (mem_Ioc.mp hb).1
        simp only [mem_Ioc] at hnot
        omega
      rw [Nat.mul_comm a b, hz b a hbB (mem_Ioc.mp ha).1, mul_zero]

/-- An unsigned bound for the entire high-high rectangle, retaining its boundary width. -/
theorem abs_logMobiusTailBilinearSquareAction_le_boundary {N U B : ℕ}
    (hUN : U ≤ N) (hUB : U ≤ B) (hB : B ≤ N ^ 2)
    (hcap : N ^ 2 ≤ (U + 1) * B) (hclose : N ^ 2 < 2 * (U + 1) ^ 2) :
    |logMobiusTailBilinearSquareAction N U| ≤
      2 * ((B - U : ℕ) : ℝ) ^ 2 * ((N - U : ℕ) : ℝ) * Real.log N := by
  rw [square_cutoff_tail_restrict hUB hB hcap]
  simp_rw [mul_sum]
  have hterm (a b : ℕ) (ha : a ∈ Ioc U B) (hb : b ∈ Ioc U B) :
      |(moebius a : ℝ) * ((moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b))| ≤
        2 * ((N - U : ℕ) : ℝ) * Real.log N := by
    have hprod : (U + 1) ^ 2 ≤ a * b := by
      simpa only [pow_two] using Nat.mul_le_mul
        (show U + 1 ≤ a by have := (mem_Ioc.mp ha).1; omega)
        (show U + 1 ≤ b by have := (mem_Ioc.mp hb).1; omega)
    have hq : U ^ 2 < a * b := by nlinarith
    have hqclose : N ^ 2 < 2 * (a * b) := by nlinarith
    have hma : |(moebius a : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    have hmb : |(moebius b : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
    have hk0 := mobiusSquareShortBilinearKernel_nonneg N (a * b)
    calc
      _ = |(moebius a : ℝ)| * |(moebius b : ℝ)| * mobiusSquareShortBilinearKernel N (a * b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk0]
        ring
      _ ≤ 1 * mobiusSquareShortBilinearKernel N (a * b) :=
        mul_le_mul_of_nonneg_right (mul_le_one₀ hma (abs_nonneg _) hmb) hk0
      _ ≤ _ := by simpa using mobiusSquareShortBilinearKernel_le_boundary hUN hq hqclose
  calc
    _ ≤ ∑ a ∈ Ioc U B, ∑ b ∈ Ioc U B,
        |(moebius a : ℝ) * ((moebius b : ℝ) * mobiusSquareShortBilinearKernel N (a * b))| := by
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a ∈ Ioc U B, ∑ _b ∈ Ioc U B,
        2 * ((N - U : ℕ) : ℝ) * Real.log N := by
      apply sum_le_sum
      intro a ha
      exact sum_le_sum fun b hb => hterm a b ha hb
    _ = _ := by simp; ring

theorem abs_logMobiusTailBilinearSquareAction_le_cubic {U H : ℕ}
    (hN : 2 ≤ U + H) (hH : 4 * H ≤ U + H) :
    |logMobiusTailBilinearSquareAction (U + H) U| ≤
      18 * (H : ℝ) ^ 3 * Real.log (U + H) := by
  have h3 : 3 * H ≤ U := by omega
  have hHU : H ≤ U := by omega
  have hmul1 := Nat.mul_le_mul_right U h3
  have hmul2 := Nat.mul_le_mul_right H hHU
  have hclose : (U + H) ^ 2 < 2 * (U + 1) ^ 2 := by nlinarith
  have hcap : (U + H) ^ 2 ≤ (U + 1) * (U + 3 * H) := by nlinarith
  have hB : U + 3 * H ≤ (U + H) ^ 2 := by nlinarith
  have hh := abs_logMobiusTailBilinearSquareAction_le_boundary
    (N := U + H) (U := U) (B := U + 3 * H) (by omega) (by omega) hB hcap hclose
  calc
    _ ≤ 2 * ((U + 3 * H - U : ℕ) : ℝ) ^ 2 * ((U + H - U : ℕ) : ℝ) *
        Real.log (U + H : ℕ) := hh
    _ = _ := by
      simp only [Nat.add_sub_cancel_left, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
      ring

theorem mobiusCutoffBilinearSquareSource_self (N : ℕ) :
    mobiusCutoffBilinearSquareSource N N = mobiusShortBilinearSquareSource N := by
  simp only [mobiusCutoffBilinearSquareSource, mobiusShortBilinearSquareSource,
    logMobiusCutoffBilinearSquareAction, logMobiusShortBilinearSquareAction, mul_sum, mul_assoc]

/-- The entire small-modulus action is uniform in its cutoff, including its explicit mean. -/
theorem exists_abs_logMobiusQuadraticResidueAction_le_mul :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N U : ℕ, U ≤ N →
      |logMobiusQuadraticResidueAction N U| ≤ C * (N : ℝ) * U := by
  obtain ⟨S, hS0, hS⟩ := exists_abs_sum_moebius_log_div_le
  refine ⟨S + 16384, by positivity, ?_⟩
  intro N U hUN
  by_cases hU : U = 0
  · simp [hU, logMobiusQuadraticResidueAction]
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  let W : ℝ := ∑ d ∈ Icc 1 U,
    ((moebius d : ℝ) * Real.log d) * (1 - 1 / (d : ℝ))
  have hmU : (U : ℝ) / 2 * |W| ≤ S * (U : ℝ) ^ 2 := by
    simpa only [W, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ U / 2)] using
      abs_logMobiusQuadraticResidueMean_le hS U
  have hW : |W| ≤ 2 * S * U := by
    by_contra hn
    have hp : 0 < (U : ℝ) * (|W| - 2 * S * U) :=
      mul_pos hUpos (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hmU, hp]
  have hmN : |(N : ℝ) / 2 * W| ≤ S * (N : ℝ) * U := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N / 2)]
    calc
      _ ≤ (N : ℝ) / 2 * (2 * S * U) := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  rw [logMobiusQuadraticResidueAction, logMobiusQuadraticResidueAction_eq_mean_add_centered]
  change |(N : ℝ) / 2 * W + logMobiusCenteredQuadraticResidueAction N U| ≤ _
  calc
    _ ≤ |(N : ℝ) / 2 * W| + |logMobiusCenteredQuadraticResidueAction N U| := abs_add_le _ _
    _ ≤ S * (N : ℝ) * U + 16384 * (N : ℝ) * U :=
      add_le_add hmN (abs_logMobiusCenteredQuadraticResidueAction_le_mul hUN)
    _ = _ := by ring

/-- Shortening both factors costs only the controlled small-modulus term and a cubic boundary error. -/
theorem exists_abs_psiRemainder_squareSum_sub_cutoffBilinearSource_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U H : ℕ, 2 ≤ U + H → 4 * H ≤ U + H →
      |(∑ s ∈ Ico 1 (U + H), psiRemainder (s ^ 2)) -
          mobiusCutoffBilinearSquareSource (U + H) U| ≤
        C * (U + H : ℕ) * U + 18 * (H : ℝ) ^ 3 * Real.log (U + H) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_logMobiusQuadraticResidueAction_le_mul
  refine ⟨2 * C, by positivity, ?_⟩
  intro U H hN hH
  have hU : U ≤ (U + H) ^ 2 := by nlinarith
  have he : (∑ s ∈ Ico 1 (U + H), psiRemainder (s ^ 2)) -
      mobiusCutoffBilinearSquareSource (U + H) U =
        2 * logMobiusQuadraticResidueAction (U + H) U - logMobiusTailBilinearSquareAction (U + H) U := by
    rw [psiRemainder_squareSum_eq_cutoff_bilinear (by omega) hU]
    ring
  rw [he]
  calc
    _ ≤ |2 * logMobiusQuadraticResidueAction (U + H) U| +
        |logMobiusTailBilinearSquareAction (U + H) U| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (2 * logMobiusQuadraticResidueAction (U + H) U)
          (-logMobiusTailBilinearSquareAction (U + H) U)
    _ = 2 * |logMobiusQuadraticResidueAction (U + H) U| +
        |logMobiusTailBilinearSquareAction (U + H) U| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (C * (U + H : ℕ) * U) + 18 * (H : ℝ) ^ 3 * Real.log (U + H) :=
      add_le_add (mul_le_mul_of_nonneg_left (hC (U + H) U (by omega)) (by norm_num))
        (abs_logMobiusTailBilinearSquareAction_le_cubic hN hH)
    _ = _ := by ring

/-- Any cutoff family with a critical cubic boundary budget retains the exact one-sided RH criterion. -/
theorem riemannHypothesis_iff_mobiusCutoffBilinearSquareSource_boundedAbove
    (H : ℕ → ℕ) (hH : ∀ N : ℕ, 2 ≤ N → 4 * H N ≤ N)
    {K : ℝ} (hK : ∀ N : ℕ, 2 ≤ N → (H N : ℝ) ^ 3 * Real.log N ≤ K * (N : ℝ) ^ 2) :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      mobiusCutoffBilinearSquareSource N (N - H N) ≤ B * (N : ℝ) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_psiRemainder_squareSum_sub_cutoffBilinearSource_le
  have herr (N : ℕ) (hN : 2 ≤ N) :
      |(∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) -
          mobiusCutoffBilinearSquareSource N (N - H N)| ≤
        (C + 18 * K) * (N : ℝ) ^ 2 := by
    have hHN : H N ≤ N := by have := hH N hN; omega
    have hsum : N - H N + H N = N := Nat.sub_add_cancel hHN
    have hc := hC (N - H N) (H N) (by omega) (by rw [hsum]; exact hH N hN)
    rw [hsum] at hc
    have hsumR : ((N - H N : ℕ) : ℝ) + (H N : ℝ) = (N : ℝ) := by exact_mod_cast hsum
    rw [hsumR] at hc
    have hsmall : C * (N : ℝ) * (N - H N : ℕ) ≤ C * (N : ℝ) * N :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le N (H N)) (by positivity)
    have hk := hK N hN
    nlinarith only [hc, hsmall, hk]
  rw [GaloisForLFunctions.RHTower.riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + C + 18 * K, ?_⟩
    intro N hN
    have hb := hB N hN
    have he := (abs_le.mp (herr N hN)).1
    nlinarith only [hb, he]
  · rintro ⟨B, hB⟩
    refine ⟨B + C + 18 * K, ?_⟩
    intro N hN
    have hb := hB N hN
    have he := (abs_le.mp (herr N hN)).2
    nlinarith only [hb, he]

end RHTower
