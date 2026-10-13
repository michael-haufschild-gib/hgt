import GaloisForLFunctions.RHTower.LimitPeriodicExpSingleCharacter
import GaloisForLFunctions.RHTower.WeilBoundedDenominatorLockRH
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# A producer with limit-periodic coefficients forces the Riemann hypothesis

**Theorem** (`limitPeriodic_producer_riemannHypothesis`). Let `G` be holomorphic on `Re s > ½`
with `G' = ΦG` for a function `Φ` holomorphic there. Let `G` be continuous on `Re s ≥ ½` and equal
to `s(s − 1)Γ_ℝ(s) F(s)` on `Re s > 1`, where `F(s) = exp(Σ lam(n) n^{−s}/log n) = Σ a(n) n^{−s}`.
Suppose the coefficients are limit-periodic: `a(n) = Σ_q Ψ_q(n)` with `Ψ_q` of period `q + 1`,
`|Ψ_q| ≤ B_q` and `Σ_q √(q+1) 8^{ω(q+1)} B_q < ∞`. Then the Riemann hypothesis holds.

For one period this is the endgame of `bounded_denominator_lock_riemannHypothesis`. The weight
`8^{ω(q+1)}` is `≪_ε (q+1)^ε`, so `Σ_q (q+1)^{½+ε} B_q < ∞` suffices.

**Proof.**
* `F(s) = Σ_q Σ_{χ mod q+1} L(s, c_χ) L(s, χ)` on `Re s > 1` (`LSeries_limitPeriodic`,
  `LSeries_periodic_eq_sum`).
* *Residue.* As `s → 1⁺` only the trivial characters keep a pole, so `(s − 1)F(s) → A(1)` with
  `A(s) = Σ_q L(s, c_{q,1}) Π_{p | q+1}(1 − p^{−s})` (`tendsto_sub_one_mul_limitPeriodic`;
  domination by `2√(q+1) 2^{ω(q+1)} B_q` through Parseval over the smooth numbers). Since
  `(s − 1)F(s) → G(1) ≠ 0`, `A(1) ≠ 0`.
* `A` is holomorphic on `Re s > ½` (`differentiableOn_limitTrivialSeries`, bound `8^{ω(q+1)} B_q`).
* *One class.* Near `s = 1⁺` the trivial class coefficient `Γ_1(s) = ζ(s)A(s)` is nonzero
  (`limitCharCoeff_one_eq`). So at every level `N = k!` every other character has `Γ_ξ(s) = 0`
  (`limitPeriodic_exp_single_character`). The class decomposition
  (`norm_sub_sum_limitCharCoeff_le`) then gives `|F(s) − ζ(s)A(s)| ≤ Σ_{q ≥ k} W_q → 0`.
* `F = ζA` on an interval, hence on `Re s > 1`, and `G = s(s − 1)Γ_ℝ ζ A` on `Re s > ½`, `s ≠ 1`
  (`eq_of_eq_right_half`). A zero of `ζ` with `Re s > ½` would be a zero of `G`, but `G` has none
  (`G_ne_zero`).
-/

open Complex Filter Topology Set

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral CharacterZeroPlanting

noncomputable section

/-! ## Periodic and limit-periodic Dirichlet series -/

/-- **Character decomposition of a periodic Dirichlet series.** For `Re s > 1`,
`Σ_n Ψ(n) n^{−s} = Σ_χ L(s, c_χ) L(s, χ)`. -/
theorem LSeries_periodic_eq_sum {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => Ψ n) s = ∑ χ : DirichletCharacter ℂ M,
      LSeries (charSmoothCoeff Ψ χ) s * LSeries (fun n => χ n) s := by
  classical
  set one : ℕ →*₀ ℂ := primeValueTwist (fun _ => 1) with hone
  have hone_apply : ∀ n, n ≠ 0 → one n = 1 := by
    intro n hn
    show (if n = 0 then 0 else n.factorization.prod fun _ k => (1 : ℂ) ^ k) = 1
    rw [if_neg hn]; simp
  have hsec : ∀ χ : DirichletCharacter ℂ M, smoothSection Ψ χ one = charSmoothCoeff Ψ χ := by
    intro χ; funext m
    unfold smoothSection charSmoothCoeff
    split_ifs with hm
    · rw [hone_apply m (Nat.ne_zero_of_mem_factoredNumbers hm), mul_one]
    · rfl
  have hcB : ∀ (χ : DirichletCharacter ℂ M) n, ‖charSmoothCoeff Ψ χ n‖ ≤ ∑ a, ‖Ψ a‖ := by
    intro χ n
    unfold charSmoothCoeff
    split_ifs
    · exact norm_charSection_le Ψ χ n
    · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcS : ∀ χ : DirichletCharacter ℂ M, LSeriesSummable (charSmoothCoeff Ψ χ) s := fun χ =>
    LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨∑ a, ‖Ψ a‖, fun n _ => by
      rw [sub_self, Real.rpow_zero, mul_one]; exact hcB χ n⟩
  have hχS : ∀ χ : DirichletCharacter ℂ M, LSeriesSummable (fun r : ℕ => χ r * one r) s :=
    fun χ => LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n hn => by
      rw [norm_mul, hone_apply n hn, norm_one, mul_one, sub_self, Real.rpow_zero, mul_one]
      exact DirichletCharacter.norm_le_one χ _⟩
  have h1 : LSeries (fun n => Ψ n) s = LSeries (∑ χ : DirichletCharacter ℂ M,
      LSeries.convolution (charSmoothCoeff Ψ χ) (fun r => χ r * one r)) s := by
    refine LSeries_congr (fun {n} hn => ?_) s
    rw [Finset.sum_apply]
    have h := periodic_twist_eq_sum_convolution Ψ one hn
    rw [hone_apply n hn, mul_one] at h
    rw [h]
    simp only [hsec]
  rw [h1, LSeries_sum fun χ _ => (hcS χ).convolution (hχS χ)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [LSeries_convolution' (hcS χ) (hχS χ)]
  congr 1
  exact LSeries_congr (fun {n} hn => by simp only [hone_apply n hn, mul_one]) s

/-- **Interchanging levels and integers.** If `a(n) = Σ_q Ψ_q(n)` with `|Ψ_q| ≤ B_q` summable, then
`Σ_n a(n) n^{−s} = Σ_q Σ_n Ψ_q(n) n^{−s}` for `Re s > 1`. -/
theorem LSeries_limitPeriodic {a : ℕ → ℂ} {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ}
    (hB : ∀ q x, ‖Ψ q x‖ ≤ B q) (hBsum : Summable B)
    (hΨ : ∀ n : ℕ, n ≠ 0 → a n = ∑' q, Ψ q n) {s : ℂ} (hs : 1 < s.re) :
    LSeries a s = ∑' q, LSeries (fun n => Ψ q n) s := by
  have hB0 : ∀ q, 0 ≤ B q := fun q => (norm_nonneg _).trans (hB q 0)
  have hterm : ∀ n, LSeries.term a s n = ∑' q, LSeries.term (fun n => Ψ q n) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, tsum_zero]
    · simp only [LSeries.term_of_ne_zero hn]
      rw [hΨ n hn, tsum_div_const]
  have hr : Summable fun n : ℕ => (n : ℝ) ^ (-s.re) := Real.summable_nat_rpow.mpr (by linarith)
  have hsum : Summable (Function.uncurry fun (n q : ℕ) => LSeries.term (fun n => Ψ q n) s n) := by
    refine Summable.of_norm_bounded (Summable.mul_of_nonneg hr hBsum
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hB0) fun x => ?_
    simp only [Function.uncurry]
    rw [LSeries.norm_term_eq]
    split_ifs with hx
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hB0 _)
    · rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_left (hB x.2 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [LSeries, tsum_congr hterm, ← hsum.tsum_comm]
  rfl

/-! ## Smooth sums -/

/-- A uniform bound for the sections: `|c_χ(m)| ≤ sup |Ψ|`. -/
theorem norm_charSection_le_of_le {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {B : ℝ}
    (hB : ∀ x, ‖Ψ x‖ ≤ B) (χ : DirichletCharacter ℂ M) (m : ℕ) : ‖charSection Ψ χ m‖ ≤ B := by
  have htot : (0 : ℝ) < M.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  unfold charSection
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hb : ∀ b : (ZMod M)ˣ, ‖χ ((b : ZMod M)⁻¹) * Ψ ((m : ZMod M) * b)‖ ≤ B := by
    intro b
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans
      (hB _)
  calc ((M.totient : ℝ))⁻¹ * ‖∑ b : (ZMod M)ˣ, χ ((b : ZMod M)⁻¹) * Ψ ((m : ZMod M) * b)‖
      ≤ ((M.totient : ℝ))⁻¹ * ∑ _b : (ZMod M)ˣ, B :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb b))
          (by positivity)
    _ = B := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card_units_eq_totient]
        field_simp

/-- **Euler product over smooth numbers.** `Σ_{m M-smooth} m^{−σ} = Π_{p | M}(1 − p^{−σ})^{−1}`. -/
theorem hasSum_smooth_rpow (M : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun m : Nat.factoredNumbers M.primeFactors => (m : ℝ) ^ (-σ))
      (∏ p ∈ M.primeFactors, (1 - (p : ℝ) ^ (-σ))⁻¹) := by
  classical
  have hlt : ∀ {p : ℕ}, p.Prime → ‖rpowHom σ p‖ < 1 := by
    intro p hp
    show ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt
    M.primeFactors).2
  have hfil : M.primeFactors.filter Nat.Prime = M.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hfil] at h
  exact h

/-- If `(1 − 2^{−σ})^{−1} ≤ K`, then `Π_{p | M}(1 − p^{−σ})^{−1} ≤ K^{ω(M)}`. -/
theorem prod_inv_one_sub_rpow_le (M : ℕ) {σ K : ℝ} (hσ : 0 < σ)
    (hK : (1 - (2 : ℝ) ^ (-σ))⁻¹ ≤ K) :
    ∏ p ∈ M.primeFactors, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ K ^ M.primeFactors.card := by
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have hp := Nat.prime_of_mem_primeFactors hp
    have : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · have hp := Nat.prime_of_mem_primeFactors hp
    have hle : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
    exact (inv_anti₀ (by linarith) (by linarith)).trans hK

/-- A Dirichlet series with coefficients bounded by `K₀` and supported on `M`-smooth integers is at
most `K₀ Π_{p | M}(1 − p^{−σ})^{−1}` on `Re s = σ > 0`. -/
theorem norm_LSeries_smooth_le {M : ℕ} {c : ℕ → ℂ} {K₀ : ℝ} (hc : ∀ n, ‖c n‖ ≤ K₀)
    (hsupp : ∀ n, n ∉ Nat.factoredNumbers M.primeFactors → c n = 0) {s : ℂ} (hs : 0 < s.re) :
    ‖LSeries c s‖ ≤ K₀ * ∏ p ∈ M.primeFactors, (1 - (p : ℝ) ^ (-s.re))⁻¹ := by
  classical
  set A := Nat.factoredNumbers M.primeFactors with hA
  have hK0 : 0 ≤ K₀ := (norm_nonneg _).trans (hc 0)
  have hH := hasSum_smooth_rpow M hs
  set g : ℕ → ℝ := A.indicator fun n : ℕ => K₀ * (n : ℝ) ^ (-s.re) with hg
  have hgs : Summable g :=
    (summable_subtype_iff_indicator (f := fun n : ℕ => K₀ * (n : ℝ) ^ (-s.re)) (s := A)).mp
      (hH.summable.mul_left K₀)
  have hle : ∀ n, ‖LSeries.term c s n‖ ≤ g n := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n ∈ A
    · rw [hg, Set.indicator_of_mem hn]
      split_ifs with h0
      · exact mul_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hc n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · rw [hg, Set.indicator_of_notMem hn, hsupp n hn, norm_zero]
      split_ifs <;> simp
  have hts : Summable fun n => ‖LSeries.term c s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hgs
  calc ‖LSeries c s‖ ≤ ∑' n, ‖LSeries.term c s n‖ := norm_tsum_le_tsum_norm hts
    _ ≤ ∑' n, g n := hts.tsum_le_tsum hle hgs
    _ = ∑' m : A, K₀ * (m : ℝ) ^ (-s.re) := (tsum_subtype A _).symm
    _ = K₀ * ∏ p ∈ M.primeFactors, (1 - (p : ℝ) ^ (-s.re))⁻¹ := by
        rw [tsum_mul_left, hH.tsum_eq]

/-- **Parseval over smooth numbers.** `Σ_χ |L(s, c_χ)| ≤ √M · sup|Ψ| · Π_{p | M}(1 − p^{−σ})^{−1}`
on `Re s = σ > 0`. -/
theorem sum_norm_LSeries_charSmoothCoeff_le_smooth {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {B : ℝ}
    (hB : ∀ x, ‖Ψ x‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    ∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s‖ ≤
      Real.sqrt M * B * ∏ p ∈ M.primeFactors, (1 - (p : ℝ) ^ (-s.re))⁻¹ := by
  classical
  set A := Nat.factoredNumbers M.primeFactors with hA
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hH := hasSum_smooth_rpow M hs
  set g : ℕ → ℝ := A.indicator fun n : ℕ => (n : ℝ) ^ (-s.re) with hg
  have hgs : Summable g :=
    (summable_subtype_iff_indicator (f := fun n : ℕ => (n : ℝ) ^ (-s.re)) (s := A)).mp
      hH.summable
  have hle : ∀ (χ : DirichletCharacter ℂ M) n, ‖LSeries.term (charSmoothCoeff Ψ χ) s n‖ ≤
      ‖charSection Ψ χ n‖ * g n := by
    intro χ n
    rw [LSeries.norm_term_eq]
    by_cases hn : n ∈ A
    · rw [hg, Set.indicator_of_mem hn]
      split_ifs with h0
      · exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _)]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        unfold charSmoothCoeff; rw [if_pos hn]
    · rw [hg, Set.indicator_of_notMem hn, mul_zero]
      unfold charSmoothCoeff
      rw [if_neg hn, norm_zero]
      split_ifs <;> simp
  have hgb : ∀ (χ : DirichletCharacter ℂ M) n, ‖charSection Ψ χ n‖ * g n ≤ B * g n := fun χ n =>
    mul_le_mul_of_nonneg_right (norm_charSection_le_of_le Ψ hB χ n)
      (Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
  have hs1 : ∀ χ : DirichletCharacter ℂ M, Summable fun n => ‖charSection Ψ χ n‖ * g n :=
    fun χ => Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
      (Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n))
      (hgb χ) (hgs.mul_left B)
  have hts : ∀ χ : DirichletCharacter ℂ M,
      ‖LSeries (charSmoothCoeff Ψ χ) s‖ ≤ ∑' n, ‖charSection Ψ χ n‖ * g n := by
    intro χ
    have hts' : Summable fun n => ‖LSeries.term (charSmoothCoeff Ψ χ) s n‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hle χ) (hs1 χ)
    exact (norm_tsum_le_tsum_norm hts').trans (hts'.tsum_le_tsum (hle χ) (hs1 χ))
  calc ∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s‖
      ≤ ∑ χ : DirichletCharacter ℂ M, ∑' n, ‖charSection Ψ χ n‖ * g n :=
        Finset.sum_le_sum fun χ _ => hts χ
    _ = ∑' n, ∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ n‖ * g n :=
        (Summable.tsum_finsetSum fun χ _ => hs1 χ).symm
    _ ≤ ∑' n, Real.sqrt M * B * g n := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun χ _ => hs1 χ)
          (hgs.mul_left _)
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (sum_norm_charSection_le Ψ hB n)
          (Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
    _ = Real.sqrt M * B * ∏ p ∈ M.primeFactors, (1 - (p : ℝ) ^ (-s.re))⁻¹ := by
        rw [tsum_mul_left, hg, ← tsum_subtype A, hH.tsum_eq]

/-- `(1 − 2^{−σ})^{−1} ≤ 4` for `σ ≥ ½`. -/
theorem inv_one_sub_two_rpow_le_four {σ : ℝ} (hσ : 1 / 2 ≤ σ) : (1 - (2 : ℝ) ^ (-σ))⁻¹ ≤ 4 := by
  have h1 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow]
  have h3 : (4 / 3 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h4 : (Real.sqrt 2)⁻¹ < 3 / 4 := by
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]; linarith
  have h5 : (2 : ℝ) ^ (-σ) < 3 / 4 := by linarith
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- `(1 − 2^{−σ})^{−1} ≤ 2` for `σ ≥ 1`. -/
theorem inv_one_sub_two_rpow_le_two {σ : ℝ} (hσ : 1 ≤ σ) : (1 - (2 : ℝ) ^ (-σ))⁻¹ ≤ 2 := by
  have h1 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_neg_one] at h1
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- `|Π_{p | M}(1 − p^{−s})| ≤ 2^{ω(M)}` on `Re s ≥ 0`. -/
theorem norm_prod_one_sub_cpow_le (M : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ 2 ^ M.primeFactors.card := by
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
  have hp := Nat.prime_of_mem_primeFactors hp
  have hpn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by linarith)
  calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-! ## The trivial-class series -/

/-- `A(s) = Σ_q L(s, c_{q,1}) Π_{p | q+1}(1 − p^{−s})`, the part of `Σ_q Ψ_q` carried by `ζ`. -/
def limitTrivialSeries (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) (s : ℂ) : ℂ :=
  ∑' q, LSeries (charSmoothCoeff (Ψ q) 1) s * ∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ) ^ (-s))

theorem norm_trivialTerm_le {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {B : ℝ} (hB : ∀ x, ‖Ψ x‖ ≤ B)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖LSeries (charSmoothCoeff Ψ 1) s * ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤
      8 ^ M.primeFactors.card * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hc : ∀ n, ‖charSmoothCoeff Ψ 1 n‖ ≤ B := by
    intro n; unfold charSmoothCoeff; split_ifs
    · exact norm_charSection_le_of_le Ψ hB 1 n
    · rw [norm_zero]; exact hB0
  have hsupp : ∀ n, n ∉ Nat.factoredNumbers M.primeFactors → charSmoothCoeff Ψ 1 n = 0 := by
    intro n hn; unfold charSmoothCoeff; rw [if_neg hn]
  have h1 := norm_LSeries_smooth_le hc hsupp (by linarith : 0 < s.re)
  have h2 := prod_inv_one_sub_rpow_le M (by linarith : 0 < s.re) (inv_one_sub_two_rpow_le_four hs)
  rw [norm_mul]
  calc ‖LSeries (charSmoothCoeff Ψ 1) s‖ * ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖
      ≤ (B * 4 ^ M.primeFactors.card) * 2 ^ M.primeFactors.card :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hB0))
          (norm_prod_one_sub_cpow_le M (by linarith)) (norm_nonneg _) (by positivity)
    _ = 8 ^ M.primeFactors.card * B := by
        rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]; ring

theorem differentiableAt_LSeries_charSmoothCoeff {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (LSeries (charSmoothCoeff Ψ χ)) s := by
  have hc : ∀ n, ‖charSmoothCoeff Ψ χ n‖ ≤ ∑ a, ‖Ψ a‖ := by
    intro n; unfold charSmoothCoeff; split_ifs
    · exact norm_charSection_le Ψ χ n
    · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsupp : ∀ n, n ∉ Nat.factoredNumbers M.primeFactors → charSmoothCoeff Ψ χ n = 0 := by
    intro n hn; unfold charSmoothCoeff; rw [if_neg hn]
  have habs := abscissa_smooth_le_zero hc hsupp
  have hopen : IsOpen {z : ℂ | LSeries.abscissaOfAbsConv (charSmoothCoeff Ψ χ) < z.re} :=
    isOpen_lt continuous_const (EReal.continuous_coe_iff.mpr Complex.continuous_re)
  exact (LSeries_differentiableOn _).differentiableAt (hopen.mem_nhds
    (habs.trans_lt (by exact_mod_cast hs)))

/-- `A` is holomorphic on `Re s > ½` when `Σ_q 8^{ω(q+1)} B_q < ∞`. -/
theorem differentiableOn_limitTrivialSeries {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ}
    (hB : ∀ q x, ‖Ψ q x‖ ≤ B q)
    (h8 : Summable fun q : ℕ => (8 : ℝ) ^ (q + 1).primeFactors.card * B q) :
    DifferentiableOn ℂ (limitTrivialSeries Ψ) {s : ℂ | 1 / 2 < s.re} := by
  refine Complex.differentiableOn_tsum_of_summable_norm h8 (fun q s hs => ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun q s hs =>
      norm_trivialTerm_le (Ψ q) (hB q) (le_of_lt hs))
  have hs' : 0 < s.re := by have : (1 / 2 : ℝ) < s.re := hs; linarith
  refine ((differentiableAt_LSeries_charSmoothCoeff (Ψ q) 1 hs').mul
    (DifferentiableAt.fun_finsetProd fun p hp => ?_)).differentiableWithinAt
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl hp0))

/-- `A` is continuous on the closed half-plane `Re s ≥ ½`. -/
theorem continuousOn_limitTrivialSeries {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ}
    (hB : ∀ q x, ‖Ψ q x‖ ≤ B q)
    (h8 : Summable fun q : ℕ => (8 : ℝ) ^ (q + 1).primeFactors.card * B q) :
    ContinuousOn (limitTrivialSeries Ψ) {s : ℂ | 1 / 2 ≤ s.re} := by
  refine continuousOn_tsum (fun q s hs => ?_) h8 (fun q s hs =>
    norm_trivialTerm_le (Ψ q) (hB q) hs)
  have hs' : 0 < s.re := by have : (1 / 2 : ℝ) ≤ s.re := hs; linarith
  refine ((differentiableAt_LSeries_charSmoothCoeff (Ψ q) 1 hs').mul
    (DifferentiableAt.fun_finsetProd fun p hp => ?_)).continuousAt.continuousWithinAt
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl hp0))

/-- `|A(s)| ≤ Σ_q 8^{ω(q+1)} B_q` on `Re s ≥ ½`. -/
theorem norm_limitTrivialSeries_le {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ}
    (hB : ∀ q x, ‖Ψ q x‖ ≤ B q)
    (h8 : Summable fun q : ℕ => (8 : ℝ) ^ (q + 1).primeFactors.card * B q) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖limitTrivialSeries Ψ s‖ ≤ ∑' q : ℕ, (8 : ℝ) ^ (q + 1).primeFactors.card * B q := by
  have hle := fun q => norm_trivialTerm_le (Ψ q) (hB q) hs
  have hsum : Summable fun q => ‖LSeries (charSmoothCoeff (Ψ q) 1) s *
      ∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ) ^ (-s))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle h8
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hle h8)

/-! ## Classes of characters -/

open Classical in
/-- A character mod `M` agrees at level `MN` with at most one character mod `N`. -/
theorem sum_ite_changeLevel_eq {M N : ℕ} [NeZero (M * N)] (χ : DirichletCharacter ℂ M) (t : ℂ) :
    ∑ ξ : DirichletCharacter ℂ N,
      (if DirichletCharacter.changeLevel (dvd_mul_right M N) χ =
          DirichletCharacter.changeLevel (dvd_mul_left N M) ξ then t else 0) =
      if ∃ ξ : DirichletCharacter ℂ N, DirichletCharacter.changeLevel (dvd_mul_right M N) χ =
          DirichletCharacter.changeLevel (dvd_mul_left N M) ξ then t else 0 := by
  split_ifs with h
  · obtain ⟨ξ₀, h₀⟩ := h
    rw [Finset.sum_eq_single ξ₀ (fun ξ _ hξ => if_neg fun h' =>
      hξ (DirichletCharacter.changeLevel_injective (dvd_mul_left N M) (h'.symm.trans h₀)))
      (fun h => absurd (Finset.mem_univ _) h), if_pos h₀]
  · exact Finset.sum_eq_zero fun ξ _ => if_neg fun h' => h ⟨ξ, h'⟩

open Classical in
/-- **Class decomposition.** If every level `q + 1 ≤ k` divides `N`, the total
`Σ_q Σ_χ L(s, c_χ) L(s, χ)` differs from `Σ_{ξ mod N} Γ_ξ(s)` by at most the levels `q ≥ k`. -/
theorem norm_sub_sum_limitCharCoeff_le (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) {N : ℕ} [NeZero N]
    {k : ℕ} (hk : ∀ q < k, (q + 1) ∣ N) (s : ℂ)
    (hT : Summable fun q : ℕ => ∑ χ : DirichletCharacter ℂ (q + 1),
      ‖LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s‖) :
    ‖(∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
        LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s) -
      ∑ ξ : DirichletCharacter ℂ N, limitCharCoeff Ψ ξ s‖ ≤
      ∑' q : ℕ, if k ≤ q then ∑ χ : DirichletCharacter ℂ (q + 1),
        ‖LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s‖ else 0 := by
  set T : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ := fun q χ =>
    LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s with hTdef
  set E : (q : ℕ) → DirichletCharacter ℂ (q + 1) → Prop := fun q χ =>
    ∃ ξ : DirichletCharacter ℂ N, DirichletCharacter.changeLevel (dvd_mul_right (q + 1) N) χ =
      DirichletCharacter.changeLevel (dvd_mul_left N (q + 1)) ξ with hE
  have hsumξ : ∑ ξ : DirichletCharacter ℂ N, limitCharCoeff Ψ ξ s =
      ∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1), if E q χ then T q χ else 0 := by
    unfold limitCharCoeff
    rw [← Summable.tsum_finsetSum]
    · refine tsum_congr fun q => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun χ _ => by convert sum_ite_changeLevel_eq χ (T q χ)
    · intro ξ _
      refine Summable.of_norm_bounded hT fun q =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
  have hs1 : Summable fun q : ℕ => ∑ χ : DirichletCharacter ℂ (q + 1), T q χ :=
    Summable.of_norm_bounded hT fun q => norm_sum_le _ _
  have hs2 : Summable fun q : ℕ =>
      ∑ χ : DirichletCharacter ℂ (q + 1), if E q χ then T q χ else 0 :=
    Summable.of_norm_bounded hT fun q =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by
        split_ifs
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _)
  rw [hsumξ, ← hs1.tsum_sub hs2]
  have hdiff : ∀ q : ℕ, (∑ χ : DirichletCharacter ℂ (q + 1), T q χ) -
      ∑ χ : DirichletCharacter ℂ (q + 1), (if E q χ then T q χ else 0) =
      ∑ χ : DirichletCharacter ℂ (q + 1), (if E q χ then 0 else T q χ) := fun q => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => by split_ifs <;> ring
  simp only [hdiff]
  have hb : ∀ q : ℕ, ‖∑ χ : DirichletCharacter ℂ (q + 1), (if E q χ then 0 else T q χ)‖ ≤
      if k ≤ q then ∑ χ : DirichletCharacter ℂ (q + 1), ‖T q χ‖ else 0 := by
    intro q
    split_ifs with hkq
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl)
    · have hqN : (q + 1) ∣ N := hk q (by omega)
      rw [Finset.sum_eq_zero fun χ _ => if_pos ⟨DirichletCharacter.changeLevel hqN χ, by
        rw [← DirichletCharacter.changeLevel_trans χ hqN (dvd_mul_left N (q + 1))]⟩, norm_zero]
  have hbs : Summable fun q : ℕ =>
      if k ≤ q then ∑ χ : DirichletCharacter ℂ (q + 1), ‖T q χ‖ else 0 :=
    Summable.of_nonneg_of_le
      (fun q => by split_ifs; exacts [Finset.sum_nonneg fun _ _ => norm_nonneg _, le_rfl])
      (fun q => by split_ifs; exacts [le_rfl, Finset.sum_nonneg fun _ _ => norm_nonneg _]) hT
  have hns := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hbs
  exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum hb hbs)

/-! ## The residue at `s = 1` -/

theorem tendsto_ofReal_nhdsGT_one : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith

/-- **The residue.** `(s − 1) Σ_q Σ_χ L(s, c_χ) L(s, χ) → A(1)` as `s → 1⁺`: only the trivial
characters have a pole. -/
theorem tendsto_sub_one_mul_limitPeriodic {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ}
    (hB : ∀ q x, ‖Ψ q x‖ ≤ B q)
    (h2 : Summable fun q : ℕ => Real.sqrt ((q : ℝ) + 1) * 2 ^ (q + 1).primeFactors.card * B q) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * ∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
        LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s) (𝓝[>] 1)
      (𝓝 (limitTrivialSeries Ψ 1)) := by
  classical
  have hB0 : ∀ q, 0 ≤ B q := fun q => (norm_nonneg _).trans (hB q 0)
  have hpath := tendsto_ofReal_nhdsGT_one
  have hpath' : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
    hpath.mono_right nhdsWithin_le_nhds
  have hrw : ∀ s : ℝ, ((s : ℂ) - 1) * ∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
      LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s =
      ∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
        LSeries (charSmoothCoeff (Ψ q) χ) s * (((s : ℂ) - 1) * LSeries (fun n => χ n) s) := by
    intro s
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ _ => by ring
  simp only [hrw]
  unfold limitTrivialSeries
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun q => 2 * (Real.sqrt ((q : ℝ) + 1) * 2 ^ (q + 1).primeFactors.card * B q))
    (h2.mul_left 2) (fun q => ?_) ?_
  · -- pointwise limits
    have hχ : ∀ χ : DirichletCharacter ℂ (q + 1), Tendsto (fun s : ℝ =>
        LSeries (charSmoothCoeff (Ψ q) χ) s * (((s : ℂ) - 1) * LSeries (fun n => χ n) s))
        (𝓝[>] 1) (𝓝 (LSeries (charSmoothCoeff (Ψ q) χ) 1 *
          (if χ = 1 then ∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) else 0))) := by
      intro χ
      have hc : Tendsto (fun s : ℝ => LSeries (charSmoothCoeff (Ψ q) χ) s) (𝓝[>] 1)
          (𝓝 (LSeries (charSmoothCoeff (Ψ q) χ) 1)) :=
        (differentiableAt_LSeries_charSmoothCoeff (Ψ q) χ
          (by norm_num : (0 : ℝ) < (1 : ℂ).re)).continuousAt.tendsto.comp hpath'
      refine hc.mul ?_
      have hev : (fun s : ℝ => ((s : ℂ) - 1) * DirichletCharacter.LFunction χ s) =ᶠ[𝓝[>] 1]
          (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => χ n) s) := by
        filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
        rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hs)]
      refine Tendsto.congr' hev ?_
      split_ifs with h1
      · subst h1
        have hres := (DirichletCharacter.LFunctionTrivChar_residue_one (N := q + 1)).comp hpath
        simp only [Complex.cpow_neg_one]
        exact hres
      · have hL : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ s) (𝓝[>] 1)
            (𝓝 (DirichletCharacter.LFunction χ 1)) :=
          (DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr h1)).continuousAt.tendsto.comp
            hpath'
        have h0 : Tendsto (fun s : ℝ => (s : ℂ) - 1) (𝓝[>] 1) (𝓝 0) := by
          simpa using hpath'.sub_const (1 : ℂ)
        simpa using h0.mul hL
    have hsum := tendsto_finsetSum (Finset.univ : Finset (DirichletCharacter ℂ (q + 1)))
      fun χ _ => hχ χ
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
    exact hsum
  · -- domination on `1 < s ≤ 2`
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with
      s (hs : 1 < s) hs2 q
    have hs2' : s < 2 := hs2.2
    have hL : ∀ χ : DirichletCharacter ℂ (q + 1),
        ‖((s : ℂ) - 1) * LSeries (fun n => χ n) s‖ ≤ 2 := by
      intro χ
      have h1 := norm_LSeries_le_of_norm_le hs (f := fun n => χ n)
        (fun n => DirichletCharacter.norm_le_one χ _)
      have h2' := RHTower.Sieve.tsum_nat_rpow_neg_le hs
      have hn : ‖(s : ℂ) - 1‖ = s - 1 := by
        rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      rw [norm_mul, hn]
      have hz : zetaBound s ≤ 1 + 1 / (s - 1) := h2'
      calc (s - 1) * ‖LSeries (fun n => χ n) s‖ ≤ (s - 1) * (1 * zetaBound s) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ (s - 1) * (1 + 1 / (s - 1)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hz (by linarith)
        _ = s := by
            have h : s - 1 ≠ 0 := (sub_pos.mpr hs).ne'
            field_simp
            ring
        _ ≤ 2 := hs2'.le
    have hP := sum_norm_LSeries_charSmoothCoeff_le_smooth (Ψ q) (hB q)
      (s := (s : ℂ)) (by simp; linarith)
    have hK := prod_inv_one_sub_rpow_le (q + 1) (σ := s) (by linarith)
      (inv_one_sub_two_rpow_le_two hs.le)
    simp only [Complex.ofReal_re] at hP
    push_cast at hP
    calc ‖∑ χ : DirichletCharacter ℂ (q + 1),
          LSeries (charSmoothCoeff (Ψ q) χ) s * (((s : ℂ) - 1) * LSeries (fun n => χ n) s)‖
        ≤ ∑ χ : DirichletCharacter ℂ (q + 1), ‖LSeries (charSmoothCoeff (Ψ q) χ) s‖ * 2 :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hL χ) (norm_nonneg _))
      _ = 2 * ∑ χ : DirichletCharacter ℂ (q + 1), ‖LSeries (charSmoothCoeff (Ψ q) χ) s‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 2 * (Real.sqrt ((q : ℝ) + 1) * 2 ^ (q + 1).primeFactors.card * B q) := by
          refine mul_le_mul_of_nonneg_left (hP.trans ?_) (by norm_num)
          calc Real.sqrt ((q : ℝ) + 1) * B q *
                ∏ p ∈ (q + 1).primeFactors, (1 - (p : ℝ) ^ (-s))⁻¹
              ≤ Real.sqrt ((q : ℝ) + 1) * B q * 2 ^ (q + 1).primeFactors.card :=
                mul_le_mul_of_nonneg_left hK (mul_nonneg (Real.sqrt_nonneg _) (hB0 q))
            _ = Real.sqrt ((q : ℝ) + 1) * 2 ^ (q + 1).primeFactors.card * B q := by ring

/-! ## The theorem -/

open Classical in
/-- The coefficient of the trivial class is `ζ(s) A(s)`. -/
theorem limitCharCoeff_one_eq (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    limitCharCoeff Ψ (1 : DirichletCharacter ℂ 1) s = riemannZeta s * limitTrivialSeries Ψ s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  unfold limitCharCoeff limitTrivialSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [Finset.sum_eq_single 1]
  · rw [if_pos (by rw [map_one, map_one]), ← DirichletCharacter.LFunction_eq_LSeries _ hs]
    have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q + 1) hs1
    rw [DirichletCharacter.LFunctionTrivChar] at h
    rw [h]
    ring
  · intro χ _ hχ
    rw [if_neg fun h => hχ (DirichletCharacter.changeLevel_injective (dvd_mul_right (q + 1) 1)
      (h.trans (by rw [map_one, map_one])))]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **A producer with limit-periodic coefficients factors through `ζ`.**
Let `G` be holomorphic with `G' = ΦG` on `Re s > ½`, `Φ` holomorphic there, `G` continuous on
`Re s ≥ ½`, and `G = s(s − 1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)` on `Re s > 1`. Suppose the
Dirichlet coefficients `a = exp⋆(lam/log)` are limit-periodic: `a(n) = Σ_q Ψ_q(n)` with `Ψ_q` of
period `q + 1`, `|Ψ_q| ≤ B_q` and `Σ_q √(q+1) 8^{ω(q+1)} B_q < ∞`. Then
`G = s(s − 1)Γ_ℝ(s) ζ(s) A(s)` on `Re s > ½`, `s ≠ 1`, and `Σ a(n) n^{−s} = ζ(s) A(s)` on
`Re s > 1`, where `A` is the trivial-class series. -/
theorem limitPeriodic_producer_factor {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ} (hB : ∀ q x, ‖Ψ q x‖ ≤ B q)
    (hW : Summable fun q : ℕ =>
      Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * B q)
    (hΨ : ∀ n : ℕ, n ≠ 0 → dirichletExp (lamLog lam) n = ∑' q, Ψ q n) :
    (∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * limitTrivialSeries Ψ s)) ∧
    ∀ s : ℂ, 1 < s.re →
      LSeries (dirichletExp (lamLog lam)) s = riemannZeta s * limitTrivialSeries Ψ s := by
  classical
  set a := dirichletExp (lamLog lam) with ha
  have hB0 : ∀ q, 0 ≤ B q := fun q => (norm_nonneg _).trans (hB q 0)
  have hsq : ∀ q : ℕ, 1 ≤ Real.sqrt ((q : ℝ) + 1) := fun q =>
    Real.one_le_sqrt.mpr (le_add_of_nonneg_left (Nat.cast_nonneg q))
  have h8one : ∀ q : ℕ, (1 : ℝ) ≤ 8 ^ (q + 1).primeFactors.card := fun q =>
    one_le_pow₀ (by norm_num)
  have hBs : Summable fun q : ℕ => Real.sqrt ((q : ℝ) + 1) * B q :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (Real.sqrt_nonneg _) (hB0 q)) (fun q => by
      calc Real.sqrt ((q : ℝ) + 1) * B q
          = Real.sqrt ((q : ℝ) + 1) * 1 * B q := by ring
        _ ≤ Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * B q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h8one q) (Real.sqrt_nonneg _))
            (hB0 q)) hW
  have h2 : Summable fun q : ℕ =>
      Real.sqrt ((q : ℝ) + 1) * 2 ^ (q + 1).primeFactors.card * B q :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (by positivity)) (hB0 q)) (fun q => by
      have : (2 : ℝ) ^ (q + 1).primeFactors.card ≤ 8 ^ (q + 1).primeFactors.card :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _))
        (hB0 q)) hW
  have h8 : Summable fun q : ℕ => (8 : ℝ) ^ (q + 1).primeFactors.card * B q :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (by positivity) (hB0 q)) (fun q => by
      calc (8 : ℝ) ^ (q + 1).primeFactors.card * B q
          = 1 * 8 ^ (q + 1).primeFactors.card * B q := by ring
        _ ≤ Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * B q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsq q) (by positivity))
            (hB0 q)) hW
  have hBsum : Summable B := Summable.of_nonneg_of_le hB0
    (fun q => le_mul_of_one_le_left (hB0 q) (hsq q)) hBs
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hℓ : ∀ σ : ℝ, 1 < σ → LSeriesSummable (lamLog lam) σ := fun σ hσ =>
    lseriesSummable_of_le (norm_lamLog_le lam) hsl (by simpa using hσ)
  /- `F = Σ_q Σ_χ L(s, c_χ) L(s, χ)`. -/
  have hF : ∀ s : ℂ, 1 < s.re → LSeries a s = ∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
      LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s := by
    intro s hs
    rw [LSeries_limitPeriodic hB hBsum hΨ hs]
    exact tsum_congr fun q => LSeries_periodic_eq_sum (Ψ q) hs
  set A := limitTrivialSeries Ψ with hAdef
  have hAd := differentiableOn_limitTrivialSeries hB h8
  have hpath' : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
    tendsto_ofReal_nhdsGT_one.mono_right nhdsWithin_le_nhds
  /- The residue: `A(1) = G(1) ≠ 0`. -/
  have hA1 : A 1 = G 1 := by
    have hlim1 := tendsto_sub_one_mul_limitPeriodic hB h2
    have hGt : Tendsto (fun s : ℝ => G s / ((s : ℂ) * Gammaℝ s)) (𝓝[>] 1)
        (𝓝 (G 1 / (1 * Gammaℝ 1))) :=
      ((hGc 1 (by norm_num)).tendsto.comp hpath').div (hpath'.mul
        ((differentiableAt_Gammaℝ_of_re_pos
          (by norm_num : (0 : ℝ) < (1 : ℂ).re)).continuousAt.tendsto.comp hpath'))
        (by simp [Gammaℝ_one])
    rw [Gammaℝ_one, one_mul, div_one] at hGt
    refine tendsto_nhds_unique hlim1 (hGt.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have hsre : 1 < ((s : ℂ)).re := by simpa using hs
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have hs0 : (s : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [← hF s hsre, (hLa s hsre).2, G_eq_bigG hsl hid hGd hG2 hsre, bigG]
    field_simp
  have hA1ne : A 1 ≠ 0 := by
    rw [hA1]; exact G_ne_zero hΦd hGd hG2 (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num)
  /- `F = ζ A` at real points where `A ≠ 0`. -/
  set w : ℝ → ℕ → ℝ := fun s q => Real.sqrt ((q : ℝ) + 1) * B q * zetaBound s * zetaBound s
    with hw
  have hT : ∀ s : ℝ, 1 < s → ∀ q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
      ‖LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s‖ ≤ w s q := by
    intro s hs q
    have h1 := sum_norm_LSeries_charSmoothCoeff_le (Ψ q) (hB q) hs
    push_cast at h1
    calc ∑ χ : DirichletCharacter ℂ (q + 1),
          ‖LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s‖
        ≤ ∑ χ : DirichletCharacter ℂ (q + 1),
            ‖LSeries (charSmoothCoeff (Ψ q) χ) s‖ * zetaBound s :=
          Finset.sum_le_sum fun χ _ => by
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have := norm_LSeries_le_of_norm_le hs (f := fun n => χ n)
              (fun n => DirichletCharacter.norm_le_one χ _)
            rwa [one_mul] at this
      _ = (∑ χ : DirichletCharacter ℂ (q + 1), ‖LSeries (charSmoothCoeff (Ψ q) χ) s‖) *
            zetaBound s := by rw [Finset.sum_mul]
      _ ≤ w s q := mul_le_mul_of_nonneg_right h1 (zetaBound_nonneg s)
  have hws : ∀ s : ℝ, Summable (w s) := fun s => (hBs.mul_right _).mul_right _
  have hw0 : ∀ s : ℝ, ∀ q, 0 ≤ w s q := fun s q =>
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hB0 q)) (zetaBound_nonneg s))
      (zetaBound_nonneg s)
  have hFeq : ∀ s : ℝ, 1 < s → A s ≠ 0 → LSeries a s = riemannZeta s * A s := by
    intro s hs hAs
    have hsre : 1 < ((s : ℂ)).re := by simpa using hs
    have hΓ1 := limitCharCoeff_one_eq Ψ hsre
    have hΓ1ne : limitCharCoeff Ψ (1 : DirichletCharacter ℂ 1) s ≠ 0 := by
      rw [hΓ1]; exact mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re hsre) hAs
    have hbound : ∀ k : ℕ, ‖LSeries a s - riemannZeta s * A s‖ ≤
        ∑' q, if k ≤ q then w s q else 0 := by
      intro k
      haveI : NeZero k.factorial := ⟨Nat.factorial_ne_zero k⟩
      have hk : ∀ q < k, (q + 1) ∣ k.factorial := fun q hq =>
        Nat.dvd_factorial (Nat.succ_pos q) hq
      have h1N : (1 : DirichletCharacter ℂ k.factorial) =
          DirichletCharacter.changeLevel (Nat.one_dvd _) (1 : DirichletCharacter ℂ 1) :=
        (map_one _).symm
      have hsumξ : ∑ ξ : DirichletCharacter ℂ k.factorial, limitCharCoeff Ψ ξ s =
          riemannZeta s * A s := by
        rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ k.factorial)]
        · rw [h1N, limitCharCoeff_changeLevel]; exact hΓ1
        · intro ξ _ hξ
          rcases limitPeriodic_exp_single_character (lamLog_zero lam) (lamLog_one lam) hℓ hB hBs
            hΨ hs (ξ₁ := 1) (ξ₂ := ξ) (Ne.symm hξ) with h | h
          · exfalso; rw [h1N, limitCharCoeff_changeLevel] at h; exact hΓ1ne h
          · exact h
        · intro h; exact absurd (Finset.mem_univ _) h
      have hTs : Summable fun q : ℕ => ∑ χ : DirichletCharacter ℂ (q + 1),
          ‖LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s‖ :=
        Summable.of_nonneg_of_le (fun q => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (hT s hs) (hws s)
      have hmain := norm_sub_sum_limitCharCoeff_le Ψ hk (s : ℂ) hTs
      rw [hsumξ, ← hF s hsre] at hmain
      refine hmain.trans (Summable.tsum_le_tsum (fun q => ?_) ?_ ?_)
      · split_ifs
        · exact hT s hs q
        · exact le_rfl
      · exact Summable.of_nonneg_of_le
          (fun q => by split_ifs; exacts [Finset.sum_nonneg fun _ _ => norm_nonneg _, le_rfl])
          (fun q => by split_ifs; exacts [le_rfl, Finset.sum_nonneg fun _ _ => norm_nonneg _]) hTs
      · exact Summable.of_nonneg_of_le (fun q => by split_ifs; exacts [hw0 s q, le_rfl])
          (fun q => by split_ifs; exacts [le_rfl, hw0 s q]) (hws s)
    have htail := tendsto_tsum_tail (hws s) (hw0 s)
    have h0 : ‖LSeries a s - riemannZeta s * A s‖ ≤ 0 := ge_of_tendsto' htail hbound
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  /- `F = ζ A` on `Re s > 1`. -/
  have hAc : ContinuousAt A 1 := (hAd.differentiableAt ((isOpen_lt continuous_const
    Complex.continuous_re).mem_nhds (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num))).continuousAt
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, A s ≠ 0 :=
    (hAc.tendsto.comp hpath').eventually (isOpen_ne.mem_nhds hA1ne)
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1' : (1 : ℝ) < u := hu1
  set z₀ : ℝ := (1 + u) / 2 with hz₀
  have hz₀1 : 1 < z₀ := by rw [hz₀]; linarith
  have hz₀u : z₀ < u := by rw [hz₀]; linarith
  set U : Set ℂ := {s : ℂ | 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hLa y (by simpa using hy)).1
  have hFan : AnalyticOnNhd ℂ (LSeries a) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    have hopen : IsOpen {z : ℂ | LSeries.abscissaOfAbsConv a < z.re} :=
      isOpen_lt continuous_const (EReal.continuous_coe_iff.mpr Complex.continuous_re)
    exact ((LSeries_differentiableOn a).differentiableAt (hopen.mem_nhds
      (habs.trans_lt (by exact_mod_cast (show (1 : ℝ) < s.re from hs))))).differentiableWithinAt
  have hZAan : AnalyticOnNhd ℂ (fun s => riemannZeta s * A s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    have hs' : (1 : ℝ) < s.re := hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
    exact ((differentiableAt_riemannZeta hs1).mul (hAd.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 / 2 : ℝ) < s.re by linarith)))).differentiableWithinAt
  have hfreq : ∃ᶠ z in 𝓝[≠] (z₀ : ℂ), LSeries a z = riemannZeta z * A z := by
    have hreal : ∀ᶠ t : ℝ in 𝓝[≠] z₀, LSeries a t = riemannZeta t * A t := by
      have hI : Ioo (1 : ℝ) u ∈ 𝓝 z₀ := Ioo_mem_nhds hz₀1 hz₀u
      filter_upwards [nhdsWithin_le_nhds hI] with t ht
      exact hFeq t ht.1 (hu ht)
    have hmap : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] z₀) (𝓝[≠] (z₀ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto z₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ z₀)
        exact fun h => ht (Complex.ofReal_injective h)
    exact hmap.frequently hreal.frequently
  have hEq : Set.EqOn (LSeries a) (fun s => riemannZeta s * A s) U :=
    hFan.eqOn_of_preconnected_of_frequently_eq hZAan (convex_halfSpace_re_gt 1).isPreconnected
      (show (1 : ℝ) < ((z₀ : ℂ)).re by simpa using hz₀1) hfreq
  /- The endgame. -/
  set K : ℂ → ℂ := fun s => s * (s - 1) * Gammaℝ s * (riemannZeta s * A s)
  have hGK : ∀ s : ℂ, 1 < s.re → G s = K s := by
    intro s hs
    rw [G_eq_bigG hsl hid hGd hG2 hs, bigG, ← (hLa s hs).2, hEq hs]
  have hKd : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → DifferentiableAt ℂ K s := by
    intro s hs hs1
    have hre : 0 < s.re := by linarith
    exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (RHTower.TruncatedRadial.differentiableAt_Gammaℝ_of_re_pos hre)).mul
      ((differentiableAt_riemannZeta hs1).mul (hAd.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)))
  exact ⟨fun ρ hρ hρ1 =>
    eq_of_eq_right_half (fun s hs => (hGd s hs).differentiableAt) hKd hGK hρ hρ1,
    fun s hs => hEq hs⟩

/-- **A Herglotz producer with limit-periodic coefficients forces the Riemann hypothesis.**
Under the hypotheses of `limitPeriodic_producer_factor`, a zero of `ζ` with `Re s > ½` would be a
zero of `G = s(s − 1)Γ_ℝ ζ A`, but `G` has none. -/
theorem limitPeriodic_producer_riemannHypothesis {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ} (hB : ∀ q x, ‖Ψ q x‖ ≤ B q)
    (hW : Summable fun q : ℕ =>
      Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * B q)
    (hΨ : ∀ n : ℕ, n ≠ 0 → dirichletExp (lamLog lam) n = ∑' q, Ψ q n) :
    RiemannHypothesis := by
  have hGK_all := (limitPeriodic_producer_factor hsl hΦd hid hGc hGd hG2 hB hW hΨ).1
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  · have hs1 : s ≠ 1 := fun h => h1 (by rw [h]; simp)
    exact G_ne_zero hΦd hGd hG2 hs (by rw [hGK_all s hs hs1, hz]; ring)

end

end AbelianTwist

end RHTower
