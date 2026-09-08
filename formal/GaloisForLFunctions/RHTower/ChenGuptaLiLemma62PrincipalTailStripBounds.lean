import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalTailContour
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalFiniteStripBounds

/-!
# Chen--Gupta--Li Lemma 6.2: principal tail carrier on the deep strip

Polynomial envelopes for the factors of the continued principal tail carrier on
the deep strip `-2k ≤ Re s ≤ -1`, at every height: the Gamma--cosine
multiplier by Stirling decay above unit height and by compactness below it,
the finite Euler correction by a closed product budget, and the complementary
Dirichlet series by its elementary `M⁻¹` bound.  Combined with the all-order
Mellin decay this gives arbitrary polynomial decay of the tail carrier on
horizontal segments of the deep strip.
-/

open Complex MeasureTheory Filter Set
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- `Γ` is bounded on every compact box `a ≤ Re z ≤ b`, `|Im z| ≤ 1` with `a > 0`. -/
theorem exists_bound_norm_Gamma_low_box {a : ℝ} (b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ≤ 1 →
      ‖Complex.Gamma z‖ ≤ C := by
  have hcompact : IsCompact (Icc a b ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn Complex.Gamma (Icc a b ×ℂ Icc (-1 : ℝ) 1) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    apply ContinuousAt.continuousWithinAt
    apply Complex.continuousAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hz.1.1]
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hlo hhi him
  have hz : z ∈ Icc a b ×ℂ Icc (-1 : ℝ) 1 := by
    rw [Complex.mem_reProdIm]
    exact ⟨⟨hlo, hhi⟩, abs_le.mp him⟩
  exact (hC z hz).trans (le_max_left _ _)

/-- Polynomial growth of the regular Gamma--cosine multiplier at every height
on a strip `a ≤ Re z ≤ b` with `b < 1`. -/
theorem cglLemma62_exists_bound_principalRegularizedFactor_all_heights
    {a b : ℝ} (hb : b < 1) :
    ∃ C : ℝ, ∃ n : ℕ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤ C * (1 + |z.im|) ^ n := by
  obtain ⟨C, n, hC, hΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := 1 - b) (by linarith) (1 - a)
  obtain ⟨Cb, hCb, hbox⟩ := exists_bound_norm_Gamma_low_box (a := 1 - b) (1 - a) (by linarith)
  refine ⟨2 * C + 2 * Cb * Real.exp (Real.pi / 2), n, by positivity, ?_⟩
  intro z hlo hhi
  have hpoint : (1 : ℂ) - z = ((1 - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpow : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-(1 - z)).re = -(1 - z.re) := by simp
    rw [hre]
    calc
      (2 * Real.pi) ^ (-(1 - z.re)) ≤ (2 * Real.pi) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = 1 := Real.rpow_zero _
  have hcos : ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤
      Real.exp (Real.pi * |z.im| / 2) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    apply Real.exp_le_exp.mpr
    have him' : ((Real.pi : ℂ) * (1 - z) / 2).im = -(Real.pi * z.im / 2) := by
      simp
      ring
    rw [him', abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have hone : 0 ≤ 1 + |z.im| := by positivity
  have hpoly1 : 1 ≤ (1 + |z.im|) ^ n := one_le_pow₀ (by linarith [abs_nonneg z.im])
  unfold cglLemma62PrincipalRegularizedFunctionalFactor
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  have hΓ0 : 0 ≤ ‖Complex.Gamma (1 - z)‖ := norm_nonneg _
  have hcos0 : 0 ≤ ‖Complex.cos (Real.pi * (1 - z) / 2)‖ := norm_nonneg _
  rcases le_or_gt 1 |z.im| with him | him
  · have hΓz : ‖Complex.Gamma (1 - z)‖ ≤
        C * |z.im| ^ n * Real.exp (-(Real.pi * |z.im| / 2)) := by
      have h := hΓ (1 - z.re) (-z.im) (by linarith) (by linarith) (by rwa [abs_neg])
      rw [abs_neg] at h
      rwa [hpoint]
    have hexp : Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im| / 2) = 1 := by
      rw [← Real.exp_add]
      simp
    have hmono : |z.im| ^ n ≤ (1 + |z.im|) ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
    calc
      2 * ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z))‖ * ‖Complex.Gamma (1 - z)‖ *
          ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤
        2 * 1 * (C * |z.im| ^ n * Real.exp (-(Real.pi * |z.im| / 2))) *
          Real.exp (Real.pi * |z.im| / 2) := by
            gcongr
      _ = 2 * C * |z.im| ^ n *
          (Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im| / 2)) := by ring
      _ = 2 * C * |z.im| ^ n := by rw [hexp, mul_one]
      _ ≤ 2 * C * (1 + |z.im|) ^ n := by gcongr
      _ ≤ (2 * C + 2 * Cb * Real.exp (Real.pi / 2)) * (1 + |z.im|) ^ n := by
        have : 0 ≤ 2 * Cb * Real.exp (Real.pi / 2) * (1 + |z.im|) ^ n := by positivity
        nlinarith
  · have hΓz : ‖Complex.Gamma (1 - z)‖ ≤ Cb := by
      have h := hbox (1 - z) (by simp; linarith) (by simp; linarith) (by simp; linarith)
      exact h
    have hcos' : ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤ Real.exp (Real.pi / 2) := by
      refine hcos.trans (Real.exp_le_exp.mpr ?_)
      have : Real.pi * |z.im| ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left him.le Real.pi_pos.le
      linarith
    calc
      2 * ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z))‖ * ‖Complex.Gamma (1 - z)‖ *
          ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤
        2 * 1 * Cb * Real.exp (Real.pi / 2) := by gcongr
      _ = 2 * Cb * Real.exp (Real.pi / 2) * 1 := by ring
      _ ≤ 2 * Cb * Real.exp (Real.pi / 2) * (1 + |z.im|) ^ n := by gcongr
      _ ≤ (2 * C + 2 * Cb * Real.exp (Real.pi / 2)) * (1 + |z.im|) ^ n := by
        have : 0 ≤ 2 * C * (1 + |z.im|) ^ n := by positivity
        nlinarith

/-- Uniform budget for the principal finite Euler correction on the deep strip
`-2k ≤ Re z ≤ 1/2`. -/
def cglLemma62PrincipalCorrectionDeepBudget (Q : CGLPositiveModulus)
    (d : CGLLemma62TailContourDepth) : ℝ :=
  ∏ p ∈ Q.value.primeFactors, (4 * (1 + (p : ℝ) ^ (2 * (d.value : ℝ))))

theorem cglLemma62PrincipalCorrectionDeepBudget_nonneg (Q : CGLPositiveModulus)
    (d : CGLLemma62TailContourDepth) :
    0 ≤ cglLemma62PrincipalCorrectionDeepBudget Q d := by
  unfold cglLemma62PrincipalCorrectionDeepBudget
  exact Finset.prod_nonneg fun p _ => by positivity

private theorem cglLemma62_principal_leftFactor_norm_le_deep
    (Q : CGLPositiveModulus) (d : CGLLemma62TailContourDepth)
    {z : ℂ} (hz : -2 * (d.value : ℝ) ≤ z.re) :
    ‖cglLemma62PrincipalEulerLeftFactorAt Q z‖ ≤
      ∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ) ^ (2 * (d.value : ℝ))) := by
  unfold cglLemma62PrincipalEulerLeftFactorAt
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) ?_
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  have hpow : ‖(p : ℂ) ^ (-z)‖ ≤ (p : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hpprime.pos]
    have hre : (-z).re = -z.re := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_exponent_le hpone (by linarith)
  calc
    ‖1 - (p : ℂ) ^ (-z)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ) ^ (2 * (d.value : ℝ)) := by rw [norm_one]; linarith

/-- The principal finite Euler correction is uniformly bounded on the deep
strip. -/
theorem norm_cglLemma62PrincipalEulerCorrectionAt_le_deep
    (Q : CGLPositiveModulus) (d : CGLLemma62TailContourDepth)
    {z : ℂ} (hlo : -2 * (d.value : ℝ) ≤ z.re) (hhi : z.re ≤ 1 / 2) :
    ‖cglLemma62PrincipalEulerCorrectionAt Q z‖ ≤
      cglLemma62PrincipalCorrectionDeepBudget Q d := by
  have hleft := cglLemma62_principal_leftFactor_norm_le_deep Q d hlo
  have hright := cglLemma62_principal_rightFactor_norm_ge Q hhi
  have hq : (0 : ℝ) < (1 / 4 : ℝ) ^ Q.value.primeFactors.card := by positivity
  have hbudget : cglLemma62PrincipalCorrectionDeepBudget Q d =
      (∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ) ^ (2 * (d.value : ℝ)))) /
        (1 / 4 : ℝ) ^ Q.value.primeFactors.card := by
    unfold cglLemma62PrincipalCorrectionDeepBudget
    rw [Finset.prod_mul_distrib, Finset.prod_const, eq_div_iff (ne_of_gt hq)]
    have h4 : (4 : ℝ) ^ Q.value.primeFactors.card * (1 / 4 : ℝ) ^ Q.value.primeFactors.card = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (4 : ℝ) ^ Q.value.primeFactors.card *
          (∏ x ∈ Q.value.primeFactors, (1 + (x : ℝ) ^ (2 * (d.value : ℝ)))) *
          (1 / 4 : ℝ) ^ Q.value.primeFactors.card =
        (∏ x ∈ Q.value.primeFactors, (1 + (x : ℝ) ^ (2 * (d.value : ℝ)))) *
          ((4 : ℝ) ^ Q.value.primeFactors.card * (1 / 4 : ℝ) ^ Q.value.primeFactors.card) := by
            ring
      _ = _ := by rw [h4, mul_one]
  unfold cglLemma62PrincipalEulerCorrectionAt
  rw [norm_div, hbudget]
  have hrpos : 0 < ‖cglLemma62PrincipalEulerRightFactorAt Q z‖ := lt_of_lt_of_le hq hright
  rw [div_le_div_iff₀ hrpos hq]
  exact mul_le_mul hleft hright hq.le (Finset.prod_nonneg fun p _ => by positivity)

/-- Elementary uniform bound for the complementary trivial-character series
on the half-plane `Re s ≥ 2`. -/
theorem norm_cglLemma62DirichletTail_one_le
    (Q : CGLPositiveModulus) (J : CGLLemma62TailCutoff)
    (s : CGLAbsoluteConvergencePoint) (hs : 2 ≤ s.1.re) :
    ‖cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) J.value s‖ ≤
      (J.value : ℝ) ^ (-(1 : ℝ)) := by
  let q : ℝ := -1
  have hq : q < 0 := by norm_num [q]
  have hweight : Summable (fun k : ℕ =>
      ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q - 1)) :=
    GaloisForLFunctions.HTGeometry.summable_shift_rpow hq J.value
  have hterm : Summable (fun n : ℕ =>
      LSeries.term (↗(1 : DirichletCharacter ℂ Q.value)) s.1 n) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ Q.value) s.2
  have htailnorm : Summable (fun k : ℕ =>
      ‖LSeries.term (↗(1 : DirichletCharacter ℂ Q.value)) s.1 (k + (J.value + 1))‖) := by
    have hshift := (summable_nat_add_iff (f := fun n : ℕ =>
        ‖LSeries.term (↗(1 : DirichletCharacter ℂ Q.value)) s.1 n‖) (J.value + 1)).mpr hterm.norm
    exact hshift
  rw [cglLemma62_dirichletTail_eq_tsum_shift (1 : DirichletCharacter ℂ Q.value) J.value s]
  refine (norm_tsum_le_tsum_norm htailnorm).trans ?_
  refine (htailnorm.tsum_mono hweight ?_).trans ?_
  · intro k
    let n : ℕ := k + (J.value + 1)
    have hn : n ≠ 0 := by
      dsimp [n]
      omega
    have hχ : ‖(1 : DirichletCharacter ℂ Q.value) n‖ ≤ ‖(1 : ℂ)‖ := by
      simpa using (1 : DirichletCharacter ℂ Q.value).norm_le_one n
    have hle : ‖LSeries.term (↗(1 : DirichletCharacter ℂ Q.value)) s.1 n‖ ≤
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ :=
      LSeries.norm_term_le (f := (↗(1 : DirichletCharacter ℂ Q.value)))
        (g := fun _ : ℕ => (1 : ℂ)) s.1 hχ
    have hnorm : ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ =
        1 / (n : ℝ) ^ s.1.re := by
      rw [LSeries.norm_term_eq, if_neg hn]
      norm_num
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.1.re := by
      exact Real.rpow_le_rpow_of_exponent_le hn1 hs
    have hpowpos : 0 < (n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    have hdiv : 1 / (n : ℝ) ^ s.1.re ≤ 1 / (n : ℝ) ^ (2 : ℝ) :=
      one_div_le_one_div_of_le hpowpos hpow
    change ‖LSeries.term (↗(1 : DirichletCharacter ℂ Q.value)) s.1 n‖ ≤ _
    calc
      ‖LSeries.term (↗(1 : DirichletCharacter ℂ Q.value)) s.1 n‖ ≤
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ := hle
      _ = 1 / (n : ℝ) ^ s.1.re := hnorm
      _ ≤ 1 / (n : ℝ) ^ (2 : ℝ) := hdiv
      _ = ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q - 1) := by
        have hncast : (n : ℝ) = (J.value : ℝ) + 1 + (k : ℝ) := by
          dsimp [n]
          push_cast
          ring
        rw [hncast, one_div]
        rw [← Real.rpow_neg (by positivity : 0 ≤ (J.value : ℝ) + 1 + (k : ℝ))]
        dsimp [q]
        congr 1
        ring
  · simpa [q] using
      GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le hq J.one_le

/-- Nonnegativity of the uniform all-order Mellin budget on the tail rectangle. -/
theorem cglLemma62TailMellinUniformBudget_nonneg (w : CGLRealSmoothBump)
    (d : CGLLemma62TailContourDepth) (n : ℕ) :
    0 ≤ cglLemma62TailMellinUniformBudget w d n := by
  dsimp [cglLemma62TailMellinUniformBudget]
  apply integral_nonneg
  intro u
  unfold deningerMeyerBoundedMellinMajorant
  positivity

/-- Arbitrary polynomial decay of the continued principal tail carrier on
horizontal segments of the deep strip, above unit height. -/
theorem cglLemma62_exists_principalTail_strip_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, -2 * (d.value : ℝ) ≤ x → x ≤ -1 → 1 ≤ |y| →
      ‖cglLemma62PrincipalTailContourIntegrand w N Q t M.value
        ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / |y| ^ r := by
  obtain ⟨Cχ, n, hCχ, hχ⟩ :=
    cglLemma62_exists_bound_principalRegularizedFactor_all_heights
      (a := -2 * (d.value : ℝ)) (b := -1) (by norm_num)
  have hK := cglLemma62TailMellinUniformBudget_nonneg w d (n + r)
  have hE := cglLemma62PrincipalCorrectionDeepBudget_nonneg Q d
  have hNone : 1 ≤ (N.value : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt N.positive))
  refine ⟨cglLemma62TailMellinUniformBudget w d (n + r) * (Cχ * (1 + |t|) ^ n * 2 ^ n) *
    cglLemma62PrincipalCorrectionDeepBudget Q d, by positivity, ?_⟩
  intro x y hxlo hxhi hy
  have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
  let p : CGLLemma62TailMellinPoint d := ⟨x, y, hxlo, hxhi⟩
  have hkernel0 := cglLemma62_mellinTransform_tail_uniformAllOrderDecay w d (n + r) p
  have hkernel : ‖cglLemma62MellinTransform w ((x : ℂ) + (y : ℂ) * I)‖ ≤
      cglLemma62TailMellinUniformBudget w d (n + r) / |y| ^ (n + r) := by
    apply (le_div_iff₀ (pow_pos hypos (n + r))).mpr
    simpa [p, mul_comm] using hkernel0
  have hNpow : ‖(N.value : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos N.positive]
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    rw [hre]
    calc
      (N.value : ℝ) ^ x ≤ (N.value : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
      _ = 1 := Real.rpow_zero _
  have hshift : ((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I = (x : ℂ) + ((y - t : ℝ) : ℂ) * I := by
    push_cast; ring
  have hχz : ‖cglLemma62PrincipalRegularizedFunctionalFactor
      (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ n * 2 ^ n * |y| ^ n := by
    rw [hshift]
    have h := hχ ((x : ℂ) + ((y - t : ℝ) : ℂ) * I) (by simpa using hxlo) (by simpa using hxhi)
    have him : (((x : ℂ) + ((y - t : ℝ) : ℂ) * I)).im = y - t := by simp
    rw [him] at h
    refine h.trans ?_
    have hyt' : 1 + |y - t| ≤ (1 + |t|) * (2 * |y|) := by
      have h1 : |y - t| ≤ |y| + |t| := abs_sub _ _
      nlinarith [abs_nonneg t, abs_nonneg y]
    have hpow := pow_le_pow_left₀ (by positivity) hyt' n
    rw [mul_pow, mul_pow] at hpow
    calc
      Cχ * (1 + |y - t|) ^ n ≤ Cχ * ((1 + |t|) ^ n * (2 ^ n * |y| ^ n)) :=
        mul_le_mul_of_nonneg_left hpow hCχ
      _ = _ := by ring
  have hEz : ‖cglLemma62PrincipalEulerCorrectionAt Q (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ ≤
      cglLemma62PrincipalCorrectionDeepBudget Q d := by
    rw [hshift]
    exact norm_cglLemma62PrincipalEulerCorrectionAt_le_deep Q d (by simpa using hxlo)
      (by simp; linarith)
  have hre2 : 1 < (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I).re := by
    simp
    linarith
  let sAC : CGLAbsoluteConvergencePoint := ⟨1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I, hre2⟩
  have hT : ‖DirichletCharacter.LFunctionTrivChar Q.value (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I) -
      cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M.value
        (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I)‖ ≤ 1 := by
    have heq := cglLemma62_principal_lfunction_sub_head_eq_tail Q M.value sAC
    change ‖DirichletCharacter.LFunctionTrivChar Q.value sAC.1 -
      cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M.value sAC.1‖ ≤ 1
    rw [heq]
    refine (norm_cglLemma62DirichletTail_one_le Q M sAC ?_).trans ?_
    · show 2 ≤ (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I).re
      simp
      linarith
    · have hM1 : (1 : ℝ) ≤ M.value := by exact_mod_cast M.one_le
      rw [Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hM1
  unfold cglLemma62PrincipalTailContourIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    ‖cglLemma62MellinTransform w ((x : ℂ) + (y : ℂ) * I)‖ *
        ‖(N.value : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ *
        ‖cglLemma62PrincipalRegularizedFunctionalFactor (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ *
        ‖cglLemma62PrincipalEulerCorrectionAt Q (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ *
        ‖DirichletCharacter.LFunctionTrivChar Q.value (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I) -
          cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M.value
            (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I)‖ ≤
      (cglLemma62TailMellinUniformBudget w d (n + r) / |y| ^ (n + r)) * 1 *
        (Cχ * (1 + |t|) ^ n * 2 ^ n * |y| ^ n) *
        cglLemma62PrincipalCorrectionDeepBudget Q d * 1 := by
          gcongr
    _ = cglLemma62TailMellinUniformBudget w d (n + r) * (Cχ * (1 + |t|) ^ n * 2 ^ n) *
        cglLemma62PrincipalCorrectionDeepBudget Q d / |y| ^ r := by
          field_simp
          have hp : |y| ^ n * |y| ^ r = |y| ^ (n + r) := (pow_add |y| n r).symm
          rw [← hp]
          ring

end

end RHTower
