import GaloisForLFunctions.RHTower.WeilConeResonanceMoments

/-!
# The resonance budget of the Weil cone

Let `λ` be full-cone Weil-positive and `½ < σ₀ ≤ 3/4`. For every finite set `P` of primes,

`Σ_{C ⊆ P} λ(∏C) (∏C)^{−σ₀} 2^{−|C|} ≤ K₁ + K₂ log ∏_{p∈P} p`   (`resonance_budget`),

with `K₁, K₂` depending only on `λ` and `σ₀`. Here `∏C` runs over the squarefree products of
primes in `P` (the term `C = ∅` vanishes, as `λ` is read on `n ≥ 2`).

**Proof.** Expand the resonator: `W_P(t) = ∏_{p∈P} |1 + p^{it}|²` equals
`Σ_{C⊆P} Σ_{A⊆C} 2^{|P∖C|} (∏A / ∏(C∖A))^{it}`. The twisted first moments of `D` on
`Re s = σ₀` (`exists_norm_integral_lamSeriesCont_sub_le`) give the main term
`[∏(C∖A) ∣ ∏A] λ(∏A/∏(C∖A)) (·)^{−σ₀} T`. Disjoint prime sets divide only when `C∖A = ∅`, so
`∫ D W_P = T Σ_{C⊆P} 2^{|P∖C|} λ(∏C)(∏C)^{−σ₀} + O(Q^{O(1)} log T)`, with `Q = ∏_{p∈P} p`.
Herglotz positivity gives `Re D(σ₀ + it) ≤ K log(2T + 3) + 1` (`exists_re_lamSeriesCont_le`),
and `W_P ≥ 0` has mass `2^{|P|} T + O(Q⁴)`. Take `T = 2Q⁸`.

**Corollary** (`exists_squarefree_lt`). For every `c > 0` and `n₀` there is a squarefree `n > n₀`
with `λ(n) < c`. Indeed, `λ ≥ c` on the squarefree numbers above `n₀` would make the left side
at least `c(∏_{n₀<p≤y}(1 + 1/(2p^{3/4})) − 1) ≥ c(exp(y^{1/4}/C) − 1)`. That beats `K₂ θ(y)`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

namespace RHTower.WeilResonance

local notation "eχ" => _root_.GaloisForLFunctions.expChar

variable {lam : ℕ → ℝ}

/-! ## Expanding the resonator -/

/-- `∏_{p∈C} p` as a natural number. -/
abbrev nprod (C : Finset ℕ) : ℕ := ∏ p ∈ C, p

theorem nprod_pos {C : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) : 1 ≤ nprod C :=
  Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => (hC p hp).ne_zero)

theorem log_nprod {C : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) :
    Real.log (nprod C : ℝ) = ∑ p ∈ C, Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp; exact_mod_cast (hC p hp).ne_zero

theorem two_cos_eq_expChar (q t : ℝ) :
    ((2 * Real.cos (t * q) : ℝ) : ℂ) = eχ q t + eχ (-q) t := by
  have h := ZetaResonator.two_cos_mul_expChar q 0 t
  have h0 : eχ 0 t = 1 := by unfold _root_.GaloisForLFunctions.expChar; simp
  rw [h0, mul_one, zero_add, zero_sub] at h
  exact h

/-- **The resonator expansion** `W_P = Σ_{C⊆P} Σ_{A⊆C} 2^{|P∖C|} (∏A/∏(C∖A))^{it}`. -/
theorem resW_eq_sum {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (ZetaResonator.resW P t : ℂ) = ∑ C ∈ P.powerset, ∑ A ∈ C.powerset,
      (2 : ℂ) ^ (P \ C).card * eχ (Real.log (nprod A) - Real.log (nprod (C \ A))) t := by
  classical
  unfold ZetaResonator.resW
  rw [Complex.ofReal_prod]
  have h1 : ∀ p ∈ P, (((2 + 2 * Real.cos (t * Real.log p)) : ℝ) : ℂ) =
      (eχ (Real.log p) t + eχ (-Real.log p) t) + 2 := by
    intro p _
    rw [Complex.ofReal_add, two_cos_eq_expChar, Complex.ofReal_ofNat]; ring
  rw [Finset.prod_congr rfl h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCP : C ⊆ P := Finset.mem_powerset.mp hC
  have hCp : ∀ p ∈ C, p.Prime := fun p hp => hP p (hCP hp)
  rw [Finset.prod_const, Finset.prod_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAC : A ⊆ C := Finset.mem_powerset.mp hA
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => hCp p (hAC hp)
  have hDp : ∀ p ∈ C \ A, p.Prime := fun p hp => hCp p (Finset.sdiff_subset hp)
  rw [_root_.GaloisForLFunctions.prod_expChar, _root_.GaloisForLFunctions.prod_expChar,
    _root_.GaloisForLFunctions.expChar_add, log_nprod hAp, log_nprod hDp, Finset.sum_neg_distrib,
    ← sub_eq_add_neg]
  ring

/-- Disjoint sets of primes: `∏(C∖A) ∣ ∏A` only if `C∖A = ∅`. -/
theorem sdiff_eq_empty_of_dvd {C A : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) (hAC : A ⊆ C)
    (h : nprod (C \ A) ∣ nprod A) : C \ A = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hpP : p.Prime := hC p (Finset.sdiff_subset hp)
  have hpd : p ∣ nprod (C \ A) := Finset.dvd_prod_of_mem _ hp
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpP.prime (fun q => q)).mp (hpd.trans h)
  have hqP : q.Prime := hC q (hAC hq)
  have : p = q := (Nat.prime_dvd_prime_iff_eq hpP hqP).mp hpq
  exact (Finset.mem_sdiff.mp hp).2 (this ▸ hq)

/-! ## Sizes -/

theorem primeProd_eq_nprod (P : Finset ℕ) : ZetaResonator.primeProd P = (nprod P : ℝ) := by
  unfold ZetaResonator.primeProd; rw [Nat.cast_prod]

theorem nprod_le_primeProd {P C : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hCP : C ⊆ P) :
    (nprod C : ℝ) ≤ ZetaResonator.primeProd P := by
  rw [primeProd_eq_nprod]
  exact_mod_cast Nat.le_of_dvd (nprod_pos hP) (Finset.prod_dvd_prod_of_subset _ _ _ hCP)

theorem pow_card_le_primeProd {P : Finset ℕ} {b : ℕ} (k : ℕ) (hb : ∀ p ∈ P, b ≤ p ^ k) :
    (b : ℝ) ^ P.card ≤ ZetaResonator.primeProd P ^ k := by
  unfold ZetaResonator.primeProd
  rw [← Finset.prod_pow, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun p hp => ?_
  exact_mod_cast hb p hp

theorem sum_sum_two_pow_le (P : Finset ℕ) :
    ∑ C ∈ P.powerset, ∑ _A ∈ C.powerset, (2 : ℝ) ^ (P \ C).card ≤ (8 : ℝ) ^ P.card := by
  have h : ∀ C ∈ P.powerset, ∑ _A ∈ C.powerset, (2 : ℝ) ^ (P \ C).card ≤
      (2 : ℝ) ^ P.card * (2 : ℝ) ^ P.card := by
    intro C hC
    have hCP := Finset.mem_powerset.mp hC
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    push_cast
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hCP))
      (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.sdiff_subset))
      (by positivity) (by positivity)
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num, mul_pow, mul_pow]
  ring

/-! ## The integral of `D` against the resonator -/

/-- The main term `[d ∣ m] λ(m/d)(m/d)^{−σ₀} T` of a twisted moment. -/
def twistMain (lam : ℕ → ℝ) (σ₀ T : ℝ) (m d : ℕ) : ℂ :=
  if d ∣ m then ((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-σ₀) * T : ℝ) : ℂ) else 0

theorem sum_twistMain_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (σ₀ T : ℝ) :
    ∑ C ∈ P.powerset, ∑ A ∈ C.powerset, (2 : ℂ) ^ (P \ C).card *
        twistMain lam σ₀ T (nprod A) (nprod (C \ A)) =
      ∑ C ∈ P.powerset, (2 : ℂ) ^ (P \ C).card *
        ((lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * T : ℝ) : ℂ) := by
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCP := Finset.mem_powerset.mp hC
  have hCp : ∀ p ∈ C, p.Prime := fun p hp => hP p (hCP hp)
  rw [Finset.sum_eq_single C]
  · have h1 : nprod (C \ C) = 1 := by simp [nprod]
    rw [twistMain, h1, if_pos (one_dvd _), Nat.div_one]
  · intro A hA hAC
    have hA' := Finset.mem_powerset.mp hA
    rw [twistMain, if_neg, mul_zero]
    intro h
    have := sdiff_eq_empty_of_dvd hCp hA' h
    exact hAC (Finset.Subset.antisymm hA' (Finset.sdiff_eq_empty_iff_subset.mp this))
  · intro h; exact absurd (Finset.mem_powerset.mpr le_rfl) h

theorem continuous_lamSeriesCont_line (hW : WeilPositiveFull lam) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    (hσ₁ : σ₀ < 1) : Continuous fun t : ℝ => lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) := by
  have hl : Continuous fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hre : 1 / 2 < ((σ₀ : ℂ) + (t : ℂ) * I).re := by simp; linarith
  have hne : (σ₀ : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  exact ContinuousAt.comp (g := lamSeriesCont hW)
    (differentiableAt_lamSeriesCont hW hre hne).continuousAt hl.continuousAt

theorem continuous_expChar'' (ξ : ℝ) : Continuous (eχ ξ) := by
  unfold _root_.GaloisForLFunctions.expChar; fun_prop

theorem integral_mul_resW_eq_sum {f : ℝ → ℂ} (hf : Continuous f) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (T : ℝ) :
    ∫ t in T..(2 * T), f t * (ZetaResonator.resW P t : ℂ) =
      ∑ C ∈ P.powerset, ∑ A ∈ C.powerset, (2 : ℂ) ^ (P \ C).card *
        ∫ t in T..(2 * T), f t * eχ (Real.log (nprod A) - Real.log (nprod (C \ A))) t := by
  simp_rw [resW_eq_sum hP, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun C _ => ?_]
  · refine Finset.sum_congr rfl fun C _ => ?_
    rw [intervalIntegral.integral_finsetSum fun A _ => ?_]
    · refine Finset.sum_congr rfl fun A _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by ring
    · exact (hf.mul (continuous_const.mul (continuous_expChar'' _))).intervalIntegrable _ _
  · exact (continuous_finsetSum _ fun A _ =>
      hf.mul (continuous_const.mul (continuous_expChar'' _))).intervalIntegrable _ _

/-- The main term `T Σ_{C⊆P} 2^{|P∖C|} λ(∏C)(∏C)^{−σ₀}`. -/
theorem norm_integral_resW_sub_le (hW : WeilPositiveFull lam) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    (hσ₀' : σ₀ ≤ 3 / 4) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ {m d : ℕ}, 1 ≤ m → 1 ≤ d → ∀ {T : ℝ}, 2 ≤ T →
      ‖(∫ t in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
          eχ (Real.log m - Real.log d) t) - twistMain lam σ₀ T m d‖ ≤
        Cm * ((m : ℝ) * d) ^ 4 * (1 + Real.log (2 * T + 4)))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {T : ℝ} (hT : 2 ≤ T) :
    ‖(∫ t in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
        (ZetaResonator.resW P t : ℂ)) -
      ∑ C ∈ P.powerset, (2 : ℂ) ^ (P \ C).card *
        ((lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * T : ℝ) : ℂ)‖ ≤
      (8 : ℝ) ^ P.card * (Cm * ZetaResonator.primeProd P ^ 4 * (1 + Real.log (2 * T + 4))) := by
  have hlog : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  set B := Cm * ZetaResonator.primeProd P ^ 4 * (1 + Real.log (2 * T + 4)) with hB
  rw [integral_mul_resW_eq_sum (continuous_lamSeriesCont_line hW hσ₀ (by linarith)) hP,
    ← sum_twistMain_eq hP, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (sum_sum_two_pow_le P) (by positivity))
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun C hC => ?_
  have hCP := Finset.mem_powerset.mp hC
  have hCp : ∀ p ∈ C, p.Prime := fun p hp => hP p (hCP hp)
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A hA => ?_)
  have hAC := Finset.mem_powerset.mp hA
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => hCp p (hAC hp)
  have hDp : ∀ p ∈ C \ A, p.Prime := fun p hp => hCp p (Finset.sdiff_subset hp)
  rw [← mul_sub, norm_mul, norm_pow, Complex.norm_ofNat]
  refine mul_le_mul_of_nonneg_left ((hCm (nprod_pos hAp) (nprod_pos hDp) hT).trans ?_)
    (by positivity)
  have hprod : (nprod A : ℝ) * (nprod (C \ A)) = nprod C := by
    rw [← Nat.cast_mul, ← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hAC]
  rw [hprod, hB]
  have hCQ : (nprod C : ℝ) ≤ ZetaResonator.primeProd P := nprod_le_primeProd hP hCP
  have h1 : (0 : ℝ) ≤ nprod C := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 hCQ 4) hCm0)
    (by linarith)

theorem integral_resW_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (T : ℝ) :
    ∫ t in T..(2 * T), ZetaResonator.resW P t ≤
      (2 : ℝ) ^ P.card * T + 4 ^ P.card * ZetaResonator.primeProd P ^ 2 * 2 := by
  have h := ZetaResonator.norm_twistInt_one_sub_le (T := T) hP le_rfl le_rfl
    (ZetaResonator.coprime_one_of_prime hP)
  have he : ∀ t, eχ (Real.log ((1 : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ)) t = 1 := fun t => by
    unfold _root_.GaloisForLFunctions.expChar; simp
  have eB : ZetaResonator.twistInt (fun _ => 1) T P 1 1 =
      ((∫ t in T..(2 * T), ZetaResonator.resW P t : ℝ) : ℂ) := by
    unfold ZetaResonator.twistInt
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun t _ => by simp only [he, mul_one, one_mul]
  rw [eB, ZetaResonator.oneMain, if_pos rfl, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  simp only [Nat.cast_one, mul_one] at h
  linarith [(abs_le.mp h).2]

theorem re_integral_mul_resW_le (hW : WeilPositiveFull lam) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    (hσ₀' : σ₀ ≤ 3 / 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      (lamSeriesCont hW s).re ≤ K * Real.log (|s.im| + 3) + 1)
    (P : Finset ℕ) {T : ℝ} (hT : 2 ≤ T) :
    (∫ t in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
        (ZetaResonator.resW P t : ℂ)).re ≤
      (K * Real.log (2 * T + 3) + 1) * ∫ t in T..(2 * T), ZetaResonator.resW P t := by
  have hcD := continuous_lamSeriesCont_line hW hσ₀ (by linarith)
  have cW := ZetaResonator.continuous_resW P
  have hi : IntervalIntegrable (fun t => lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
      (ZetaResonator.resW P t : ℂ)) volume T (2 * T) :=
    (hcD.mul (Complex.continuous_ofReal.comp cW)).intervalIntegrable _ _
  have hre : (∫ t in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
      (ZetaResonator.resW P t : ℂ)).re = ∫ t in T..(2 * T),
        (lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I)).re * ZetaResonator.resW P t := by
    rw [← Complex.reCLM_apply, ← (Complex.reCLM).intervalIntegral_comp_comm hi]
    exact intervalIntegral.integral_congr fun t _ => by simp
  rw [hre, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by linarith)
    (((Complex.continuous_re.comp hcD).mul cW).intervalIntegrable _ _)
    ((continuous_const.mul cW).intervalIntegrable _ _) fun t ht => ?_
  refine mul_le_mul_of_nonneg_right ?_ (ZetaResonator.resW_nonneg P t)
  have ht0 : (0 : ℝ) ≤ t := by linarith [ht.1]
  have him : |((σ₀ : ℂ) + (t : ℂ) * I).im| = t := by
    rw [show ((σ₀ : ℂ) + (t : ℂ) * I).im = t by simp]; exact abs_of_nonneg ht0
  have hre' : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
  have h := hK ((σ₀ : ℂ) + (t : ℂ) * I) (by rw [hre']; exact hσ₀) (by rw [hre']; linarith)
    (by rw [him]; linarith [ht.1])
  rw [him] at h
  have : Real.log (t + 3) ≤ Real.log (2 * T + 3) :=
    Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
  nlinarith

/-! ## The budget -/

theorem sum_two_pow_sdiff_eq {P : Finset ℕ} (x : Finset ℕ → ℝ) :
    ∑ C ∈ P.powerset, (2 : ℝ) ^ (P \ C).card * x C =
      (2 : ℝ) ^ P.card * ∑ C ∈ P.powerset, x C * (1 / 2 : ℝ) ^ C.card := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCP := Finset.mem_powerset.mp hC
  rw [Finset.card_sdiff_of_subset hCP]
  have : (2 : ℝ) ^ P.card = 2 ^ (P.card - C.card) * 2 ^ C.card := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_card hCP)]
  rw [this, one_div, inv_pow]
  field_simp

theorem log_le_log_const_add {Q c : ℝ} (hQ : 1 ≤ Q) (hc : 0 < c) {a : ℝ} (ha : 0 < a)
    (hac : a ≤ c) : Real.log (a * Q ^ 8 + (c - a)) ≤ Real.log c + 8 * Real.log Q := by
  have hQ8 : 1 ≤ Q ^ 8 := one_le_pow₀ hQ
  rw [show 8 * Real.log Q = Real.log (Q ^ 8) by rw [Real.log_pow]; norm_num,
    ← Real.log_mul hc.ne' (by positivity)]
  exact Real.log_le_log (by nlinarith) (by nlinarith)

/-- **The resonance budget of the Weil cone.** For every full-cone Weil-positive `λ` and
`½ < σ₀ ≤ 3/4` there are `K₁, K₂` with
`Σ_{C⊆P} λ(∏C) (∏C)^{−σ₀} 2^{−|C|} ≤ K₁ + K₂ log ∏_{p∈P} p` for every finite set `P` of primes. -/
theorem resonance_budget (hW : WeilPositiveFull lam) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    (hσ₀' : σ₀ ≤ 3 / 4) :
    ∃ K₁ K₂ : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∑ C ∈ P.powerset, lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * (1 / 2 : ℝ) ^ C.card ≤
        K₁ + K₂ * Real.log (ZetaResonator.primeProd P) := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_norm_integral_lamSeriesCont_sub_le hW hσ₀ hσ₀'
  obtain ⟨K, hK0, hK⟩ := exists_re_lamSeriesCont_le hW
  refine ⟨2 * K * Real.log 7 + 2 + Cm * (9 + Real.log 8) / 2, 16 * K, fun P hP => ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ZetaResonator.primeProd P := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := hQ ▸ ZetaResonator.one_le_primeProd hP
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * Q ^ 8 := ⟨_, rfl⟩
  have hQ8 : 1 ≤ Q ^ 8 := one_le_pow₀ hQ1
  have hT2 : 2 ≤ T := by rw [hT]; linarith
  have herr := norm_integral_resW_sub_le hW hσ₀ hσ₀' hCm0
    (fun {_ _} hm hd {_} hT' => hCm hm hd hT') hP hT2
  have hre := re_integral_mul_resW_le hW hσ₀ hσ₀' hK0 hK P hT2
  have hmass := integral_resW_le hP T
  rw [← hQ] at herr hmass
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ C ∈ P.powerset, lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) *
      (1 / 2 : ℝ) ^ C.card := ⟨_, rfl⟩
  rw [← hS]
  -- the main term is real
  have hmain : ∑ C ∈ P.powerset, (2 : ℂ) ^ (P \ C).card *
      ((lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * T : ℝ) : ℂ) =
      (((2 : ℝ) ^ P.card * (S * T) : ℝ) : ℂ) := by
    have h := sum_two_pow_sdiff_eq (P := P) fun C => lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * T
    have h2 : ∑ C ∈ P.powerset, lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * T *
        (1 / 2 : ℝ) ^ C.card = S * T := by
      rw [hS, Finset.sum_mul]
      exact Finset.sum_congr rfl fun C _ => by ring
    rw [h2] at h
    rw [← h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun C _ => by push_cast; ring
  rw [hmain] at herr
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫ t in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
      (ZetaResonator.resW P t : ℂ) := ⟨_, rfl⟩
  rw [← hJ] at herr hre
  have hJlow : (2 : ℝ) ^ P.card * (S * T) - (8 : ℝ) ^ P.card *
      (Cm * Q ^ 4 * (1 + Real.log (2 * T + 4))) ≤ J.re := by
    have := (Complex.abs_re_le_norm _).trans herr
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [(abs_le.mp this).1]
  -- sizes
  have h8 : (8 : ℝ) ^ P.card ≤ Q ^ 3 := by
    rw [hQ]
    have := pow_card_le_primeProd (P := P) (b := 8) 3 fun p hp => by
      have h2 := (hP p hp).two_le
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left h2 3
    exact_mod_cast this
  have h4 : (4 : ℝ) ^ P.card ≤ Q ^ 2 := by
    rw [hQ]
    have := pow_card_le_primeProd (P := P) (b := 4) 2 fun p hp => by
      have h2 := (hP p hp).two_le
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left h2 2
    exact_mod_cast this
  have h2P : (1 : ℝ) ≤ 2 ^ P.card := one_le_pow₀ (by norm_num)
  have hlogQ : Real.log Q ≤ Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hl4 : Real.log (2 * T + 4) ≤ Real.log 8 + 8 * Real.log Q := by
    have := log_le_log_const_add hQ1 (c := 8) (a := 4) (by norm_num) (by norm_num) (by norm_num)
    rw [hT]; convert this using 2; ring
  have hl3 : Real.log (2 * T + 3) ≤ Real.log 7 + 8 * Real.log Q := by
    have := log_le_log_const_add hQ1 (c := 7) (a := 4) (by norm_num) (by norm_num) (by norm_num)
    rw [hT]; convert this using 2; ring
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hl7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  -- the error is at most `Cm (9 + log 8)/2 · 2^{|P|} T`
  have hlog4 : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  have hQ0 : 0 ≤ Q := by linarith
  have hc0 : 0 ≤ Cm * (9 + Real.log 8) / 2 := by
    have := mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 9 + Real.log 8); linarith
  have hE1 : (8 : ℝ) ^ P.card * (Cm * Q ^ 4 * (1 + Real.log (2 * T + 4))) ≤
      Cm * (9 + Real.log 8) / 2 * ((2 : ℝ) ^ P.card * T) := by
    have hlog' : 1 + Real.log (2 * T + 4) ≤ (9 + Real.log 8) * Q := by
      have := mul_le_mul_of_nonneg_left hQ1 hl8
      nlinarith
    have hCQ : 0 ≤ Cm * Q ^ 4 := mul_nonneg hCm0 (by positivity)
    have step1 : (8 : ℝ) ^ P.card * (Cm * Q ^ 4 * (1 + Real.log (2 * T + 4))) ≤
        Q ^ 3 * (Cm * Q ^ 4 * ((9 + Real.log 8) * Q)) :=
      mul_le_mul h8 (mul_le_mul_of_nonneg_left hlog' hCQ)
        (mul_nonneg hCQ (by linarith)) (pow_nonneg hQ0 3)
    have step2 : Q ^ 3 * (Cm * Q ^ 4 * ((9 + Real.log 8) * Q)) =
        Cm * (9 + Real.log 8) / 2 * T := by rw [hT]; ring
    have step3 : Cm * (9 + Real.log 8) / 2 * T ≤
        Cm * (9 + Real.log 8) / 2 * ((2 : ℝ) ^ P.card * T) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) h2P) hc0
    linarith
  have hM : ∫ t in T..(2 * T), ZetaResonator.resW P t ≤ 2 * ((2 : ℝ) ^ P.card * T) := by
    have : 4 ^ P.card * Q ^ 2 * 2 ≤ (2 : ℝ) ^ P.card * T := by
      have h1 : 4 ^ P.card * Q ^ 2 * 2 ≤ Q ^ 2 * Q ^ 2 * 2 := by
        have := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ Q ^ 2); linarith
      have h2 : Q ^ 2 * Q ^ 2 * 2 ≤ T := by
        rw [hT]; nlinarith [pow_le_pow_right₀ hQ1 (by norm_num : 4 ≤ 8)]
      nlinarith
    linarith
  have hA0 : 0 ≤ K * Real.log (2 * T + 3) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T + 3); positivity
  have hupper : J.re ≤ (K * Real.log (2 * T + 3) + 1) * (2 * ((2 : ℝ) ^ P.card * T)) :=
    hre.trans (mul_le_mul_of_nonneg_left hM hA0)
  have hpos : 0 < (2 : ℝ) ^ P.card * T := by positivity
  have hkey : S * ((2 : ℝ) ^ P.card * T) ≤ (2 * (K * Real.log (2 * T + 3) + 1) +
      Cm * (9 + Real.log 8) / 2) * ((2 : ℝ) ^ P.card * T) := by
    have e : S * ((2 : ℝ) ^ P.card * T) = (2 : ℝ) ^ P.card * (S * T) := by ring
    rw [e]; nlinarith
  have hS2 := le_of_mul_le_mul_right hkey hpos
  rw [← hQ]
  nlinarith [mul_le_mul_of_nonneg_left hl3 hK0]

/-! ## Squarefree values -/

theorem squarefree_nprod {C : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) : Squarefree (nprod C) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (hC p hp).squarefree
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hC p hp) (hC q hq)).mpr hpq)

theorem budget_term_eq (C : Finset ℕ) (σ₀ : ℝ) :
    (nprod C : ℝ) ^ (-σ₀) * (1 / 2 : ℝ) ^ C.card = ∏ p ∈ C, ((p : ℝ) ^ (-σ₀) / 2) := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod,
    Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), one_div_pow, mul_one_div]

theorem budget_sum_ge {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hPn : ∀ p ∈ P, n₀ < p)
    {c : ℝ} (hlam : ∀ n, n₀ < n → Squarefree n → c ≤ lam n) (σ₀ : ℝ) :
    c * (∏ p ∈ P, (1 + (p : ℝ) ^ (-σ₀) / 2) - 1) ≤
      ∑ C ∈ P.powerset, lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) * (1 / 2 : ℝ) ^ C.card := by
  have he := Finset.empty_mem_powerset P
  have hL : ∏ p ∈ P, (1 + (p : ℝ) ^ (-σ₀) / 2) - 1 =
      ∑ C ∈ P.powerset.erase ∅, ∏ p ∈ C, ((p : ℝ) ^ (-σ₀) / 2) := by
    rw [Finset.prod_one_add, ← Finset.sum_erase_add _ _ he, Finset.prod_empty,
      add_sub_cancel_right]
  have hR : ∑ C ∈ P.powerset, lamR lam (nprod C) * (nprod C : ℝ) ^ (-σ₀) *
      (1 / 2 : ℝ) ^ C.card = ∑ C ∈ P.powerset.erase ∅, lamR lam (nprod C) *
        (nprod C : ℝ) ^ (-σ₀) * (1 / 2 : ℝ) ^ C.card := by
    rw [← Finset.sum_erase_add _ _ he]
    simp [lamR, nprod]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_le_sum fun C hC => ?_
  have hCe := Finset.ne_of_mem_erase hC
  have hCP := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hC)
  have hCp : ∀ p ∈ C, p.Prime := fun p hp => hP p (hCP hp)
  obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hCe
  have hqC : q ≤ nprod C := Nat.le_of_dvd (nprod_pos hCp) (Finset.dvd_prod_of_mem _ hq)
  have h2 : 2 ≤ nprod C := (hCp q hq).two_le.trans hqC
  rw [mul_assoc, budget_term_eq, lamR, if_pos h2]
  exact mul_le_mul_of_nonneg_right (hlam _ ((hPn q (hCP hq)).trans_le hqC) (squarefree_nprod hCp))
    (Finset.prod_nonneg fun p _ => by positivity)

theorem theta_le_mul_sum_rpow {y : ℕ} :
    Chebyshev.theta y ≤
      (y : ℝ) ^ (3 / 4 : ℝ) * Real.log y * ∑ p ∈ Nat.primesLE y, (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpy, hpp⟩ := ZetaResonator.mem_primesLE.mp hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hpy' : (p : ℝ) ≤ y := by exact_mod_cast hpy
  have hlog : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy'
  have hr : 1 ≤ (y : ℝ) ^ (3 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, one_le_div (by positivity)]
    exact Real.rpow_le_rpow (by linarith) hpy' (by norm_num)
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  calc Real.log p ≤ Real.log y := hlog
    _ ≤ Real.log y * ((y : ℝ) ^ (3 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 4 : ℝ))) :=
        le_mul_of_one_le_right (hl0.trans hlog) hr
    _ = _ := by ring

theorem le_sum_rpow {N : ℕ} (hN : 5 ≤ N) :
    (N : ℝ) / 16 ≤ ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hN5 : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 := ZetaResonator.half_le_theta hN
  have h2 := theta_le_mul_sum_rpow (y := N ^ 8)
  have hy : (((N ^ 8 : ℕ) : ℝ)) ^ (3 / 4 : ℝ) = (N : ℝ) ^ 6 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (N : ℝ) 8, ← Real.rpow_mul hN0.le,
      ← Real.rpow_natCast (N : ℝ) 6]
    norm_num
  have hl : Real.log (((N ^ 8 : ℕ) : ℝ)) ≤ 8 * N := by
    rw [Nat.cast_pow, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hN0
    push_cast; linarith
  rw [hy] at h2
  have hS : 0 ≤ ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Finset.sum_nonneg fun p _ => by positivity
  have h3 : (N : ℝ) ^ 6 * Real.log (((N ^ 8 : ℕ) : ℝ)) *
      ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (N : ℝ) ^ 6 * (8 * N) *
      ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity)) hS
  have h4 : (N : ℝ) ^ 7 * (N / 16) ≤ (N : ℝ) ^ 7 *
      ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
    have e1 : (N : ℝ) ^ 7 * (N / 16) = (N : ℝ) ^ 8 / 2 / 8 := by ring
    have e2 : (N : ℝ) ^ 6 * (8 * N) * ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ)) =
        8 * ((N : ℝ) ^ 7 * ∑ p ∈ Nat.primesLE (N ^ 8), (p : ℝ) ^ (-(3 / 4 : ℝ))) := by ring
    rw [e1]; linarith
  exact le_of_mul_le_mul_left h4 (by positivity)

theorem exp_le_prod_one_add {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, (p : ℝ) ^ (-(3 / 4 : ℝ)) / 4) ≤
      ∏ p ∈ P, (1 + (p : ℝ) ^ (-(3 / 4 : ℝ)) / 2) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp => ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
  obtain ⟨x, hx⟩ : ∃ x, x = (p : ℝ) ^ (-(3 / 4 : ℝ)) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 ≤ x := hx ▸ by positivity
  have hx1 : x ≤ 1 := hx ▸ Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
  have h := Real.abs_exp_sub_one_sub_id_le (x := x / 4) (by rw [abs_le]; constructor <;> linarith)
  have := (abs_le.mp h).2
  nlinarith

/-- **Squarefree values of Weil-positive systems.** A full-cone Weil-positive `λ` takes values
below any `c > 0` at arbitrarily large squarefree integers. -/
theorem exists_squarefree_lt (hW : WeilPositiveFull lam) {c : ℝ} (hc : 0 < c) (n₀ : ℕ) :
    ∃ n, n₀ < n ∧ Squarefree n ∧ lam n < c := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨K₁, K₂, hK⟩ := resonance_budget hW (σ₀ := 3 / 4) (by norm_num) le_rfl
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (128 : ℝ) ^ 9 * (Nat.factorial 9) := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = M * (|K₁| + c + 2 * |K₂|) / c := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 5 (32 * (n₀ + 1 : ℝ))) B)
  have hN5 : (5 : ℝ) ≤ N := le_of_lt (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hN)
  have hNn : 32 * (n₀ + 1 : ℝ) ≤ N :=
    le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hN)
  have hNB : B < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN5' : 5 ≤ N := by exact_mod_cast hN5
  have hN1 : (1 : ℝ) ≤ N := by linarith
  -- the prime set
  obtain ⟨P, hP⟩ : ∃ P, P = (Nat.primesLE (N ^ 8)).filter (n₀ < ·) := ⟨_, rfl⟩
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => by
    rw [hP] at hp; exact ZetaResonator.primes_of_primesLE _ p (Finset.mem_of_mem_filter p hp)
  have hPn : ∀ p ∈ P, n₀ < p := fun p hp => by rw [hP] at hp; exact (Finset.mem_filter.mp hp).2
  -- upper side
  have hup := hK P hPp
  have hQ1 := ZetaResonator.one_le_primeProd hPp
  have hlQ0 : 0 ≤ Real.log (ZetaResonator.primeProd P) := Real.log_nonneg hQ1
  have hlQ : Real.log (ZetaResonator.primeProd P) ≤ 2 * (N : ℝ) ^ 8 := by
    have hsub : ZetaResonator.primeProd P ≤ ZetaResonator.primeProd (Nat.primesLE (N ^ 8)) := by
      rw [primeProd_eq_nprod, primeProd_eq_nprod]
      exact_mod_cast Nat.le_of_dvd (nprod_pos (ZetaResonator.primes_of_primesLE _))
        (Finset.prod_dvd_prod_of_subset _ _ _ (by rw [hP]; exact Finset.filter_subset _ _))
    rw [ZetaResonator.primeProd_primesLE] at hsub
    have h4 : (primorial (N ^ 8) : ℝ) ≤ (4 : ℝ) ^ (N ^ 8) := by
      exact_mod_cast primorial_le_four_pow (N ^ 8)
    have := Real.log_le_log (by linarith) (hsub.trans h4)
    rw [Real.log_pow] at this
    have := ZetaResonator.log_four_lt
    push_cast at *
    nlinarith [pow_pos (by linarith : (0 : ℝ) < N) 8]
  have hup' : ∑ C ∈ P.powerset, lamR lam (nprod C) * (nprod C : ℝ) ^ (-(3 / 4 : ℝ)) *
      (1 / 2 : ℝ) ^ C.card ≤ |K₁| + 2 * |K₂| * (N : ℝ) ^ 8 := by
    have h1 : K₂ * Real.log (ZetaResonator.primeProd P) ≤ |K₂| * (2 * (N : ℝ) ^ 8) :=
      (le_abs_self _).trans (by
        rw [abs_mul, abs_of_nonneg hlQ0]
        exact mul_le_mul_of_nonneg_left hlQ (abs_nonneg _))
    linarith [le_abs_self K₁]
  -- lower side
  have hlow := budget_sum_ge hPp hPn hcon (3 / 4)
  have hsum : (N : ℝ) / 16 - (n₀ + 1) ≤ ∑ p ∈ P, (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
    have h1 := le_sum_rpow hN5'
    rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE (N ^ 8)) (n₀ < ·)] at h1
    have h2 : ∑ p ∈ (Nat.primesLE (N ^ 8)).filter (fun p => ¬ n₀ < p),
        (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ n₀ + 1 := by
      refine (Finset.sum_le_card_nsmul _ _ 1 fun p hp => ?_).trans ?_
      · have hp := (Finset.mem_filter.mp hp).1
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (ZetaResonator.primes_of_primesLE _ p hp).one_lt.le) (by norm_num)
      · rw [nsmul_eq_mul, mul_one]
        have : ((Nat.primesLE (N ^ 8)).filter (fun p => ¬ n₀ < p)).card ≤ n₀ + 1 := by
          refine (Finset.card_le_card fun p hp => ?_).trans (Finset.card_range (n₀ + 1)).le
          rw [Finset.mem_range]; have := (Finset.mem_filter.mp hp).2; omega
        exact_mod_cast this
    rw [← hP] at h1
    linarith
  have hexp := exp_le_prod_one_add hPp
  rw [← Finset.sum_div] at hexp
  -- `exp(N/128) ≤ exp(Σ/4)`
  have hz : (N : ℝ) / 128 ≤ (∑ p ∈ P, (p : ℝ) ^ (-(3 / 4 : ℝ))) / 4 := by linarith
  have hfact := Real.pow_div_factorial_le_exp ((N : ℝ) / 128) (by positivity) 9
  have hchain : c * ((N : ℝ) ^ 9 / M - 1) ≤ |K₁| + 2 * |K₂| * (N : ℝ) ^ 8 := by
    have e : ((N : ℝ) / 128) ^ 9 / (Nat.factorial 9 : ℝ) = (N : ℝ) ^ 9 / M := by
      rw [hM, div_pow]; field_simp
    rw [e] at hfact
    have := (hfact.trans (Real.exp_le_exp.mpr hz)).trans hexp
    refine le_trans ?_ (hlow.trans hup')
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  -- contradiction with `N > B`
  have hN8 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hN1
  have hcN : M * (|K₁| + c + 2 * |K₂|) < c * N := by
    rw [hB, div_lt_iff₀ hc] at hNB; linarith
  have h1 : c * (N : ℝ) ^ 9 ≤ M * (|K₁| + c + 2 * |K₂| * (N : ℝ) ^ 8) := by
    have e : M * (c * ((N : ℝ) ^ 9 / M - 1)) = c * (N : ℝ) ^ 9 - M * c := by
      field_simp
    have := mul_le_mul_of_nonneg_left hchain hM0.le
    rw [e] at this
    nlinarith
  have h2 : M * (|K₁| + c + 2 * |K₂| * (N : ℝ) ^ 8) ≤ M * (|K₁| + c + 2 * |K₂|) * (N : ℝ) ^ 8 := by
    have : |K₁| + c ≤ (|K₁| + c) * (N : ℝ) ^ 8 :=
      le_mul_of_one_le_right (by positivity) hN8
    nlinarith [abs_nonneg K₂]
  have h3 : M * (|K₁| + c + 2 * |K₂|) * (N : ℝ) ^ 8 < c * N * (N : ℝ) ^ 8 :=
    mul_lt_mul_of_pos_right hcN (by positivity)
  have e : c * N * (N : ℝ) ^ 8 = c * (N : ℝ) ^ 9 := by ring
  linarith

end RHTower.WeilResonance
