import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakeObstructions

/-!
# Thin additions keep the count rate

Let `B₁`, `B₂` be discrete Beurling systems and `B₁ ⊕ B₂` the system with both sets of generators
(`sumSystem`).

* **Count** (`countBall_sumSystem`).  `N_{B₁⊕B₂}(x) = Σ_{|v| ≤ x} N_{B₁}(x/|v|)`, the sum over the
  generalized integers `v` of `B₂`.
* **Zeta function** (`zetaSeriesC_sumSystem`).  `ζ_{B₁⊕B₂} = ζ_{B₁} ζ_{B₂}` where both series
  converge absolutely.
* **Count rate** (`sumSystem_count_sub_le`).  If `N_{B₁}(y) = A₁ y + O(y^β)`, `β ≤ 1`, and
  `Z = Σ_v |v|^{−β} < ∞`, then `|N_{B₁⊕B₂}(x) − A₁ Z₁ x| ≤ (C₁ + A₁) Z x^β`, `Z₁ = Σ_v |v|^{−1}`:
  adding a set of generators that is thin at the exponent `β` keeps a remainder `O(x^β)`.
* **Thin sets of primes** (`summable_sFreeR_compl_rpow`).  If `Σ_{p ∈ T} p^{−β} < ∞`, the integers
  all of whose prime factors lie in `T` are summable at the exponent `β` (Euler product over the
  smooth numbers).
-/

open Complex Finset Filter Topology
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.ThinAdditions

/-! ## The count and the zeta function of a sum of systems -/

/-- The count of `B₁ ⊕ B₂`, fibred over the generalized integers of `B₂`. -/
theorem countBall_sumSystem {B₁ B₂ : BeurlingSystem} (hd₁ : B₁.IsDiscrete)
    (hd₂ : B₂.IsDiscrete) (x : ℝ) :
    (sumSystem B₁ B₂).countBall x =
      ∑ v ∈ (hd₂ x).toFinset, B₁.countBall (x / B₂.intNorm v) := by
  classical
  set Sg : Finset (Σ _ : B₂.Integer, B₁.Integer) :=
    (hd₂ x).toFinset.sigma fun v => (hd₁ (x / B₂.intNorm v)).toFinset with hSg
  set φ : (Σ _ : B₂.Integer, B₁.Integer) → Multiset (B₁.Label ⊕ B₂.Label) :=
    fun p => joinEquiv (p.2, p.1) with hφ
  have hset : {w : Multiset (B₁.Label ⊕ B₂.Label) | (sumSystem B₁ B₂).intNorm w ≤ x} =
      φ '' (Sg : Set (Σ _ : B₂.Integer, B₁.Integer)) := by
    ext w
    constructor
    · intro hw
      obtain ⟨⟨u, v⟩, rfl⟩ := (joinEquiv (α := B₁.Label) (γ := B₂.Label)).surjective w
      have hw' : B₁.intNorm u * B₂.intNorm v ≤ x := by
        rw [← intNorm_joinEquiv_sumSystem]; exact hw
      refine ⟨⟨v, u⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hSg, Finset.mem_sigma, Set.Finite.mem_toFinset,
        Set.Finite.mem_toFinset]
      exact ⟨le_trans (le_mul_of_one_le_left (B₂.intNorm_pos v).le (B₁.one_le_intNorm u)) hw',
        (le_div_iff₀ (B₂.intNorm_pos v)).mpr hw'⟩
    · rintro ⟨⟨v, u⟩, hp, rfl⟩
      rw [Finset.mem_coe, hSg, Finset.mem_sigma, Set.Finite.mem_toFinset,
        Set.Finite.mem_toFinset] at hp
      show (sumSystem B₁ B₂).intNorm (joinEquiv (u, v)) ≤ x
      rw [intNorm_joinEquiv_sumSystem]
      exact (le_div_iff₀ (B₂.intNorm_pos v)).mp hp.2
  have hinj : Function.Injective φ := by
    rintro ⟨v, u⟩ ⟨v', u'⟩ h
    have h' := (joinEquiv (α := B₁.Label) (γ := B₂.Label)).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  have hcount : (sumSystem B₁ B₂).countBall x = Sg.card := by
    show Set.ncard {w : Multiset (B₁.Label ⊕ B₂.Label) | (sumSystem B₁ B₂).intNorm w ≤ x} = _
    rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
  rw [hcount, hSg, Finset.card_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (Set.ncard_eq_toFinset_card _ (hd₁ _)).symm

/-- `ζ_{B₁⊕B₂} = ζ_{B₁} ζ_{B₂}` where both series converge absolutely. -/
theorem zetaSeriesC_sumSystem {B₁ B₂ : BeurlingSystem} {s : ℂ}
    (h₁ : Summable fun u : B₁.Integer => (B₁.intNorm u) ^ (-s.re))
    (h₂ : Summable fun v : B₂.Integer => (B₂.intNorm v) ^ (-s.re)) :
    (sumSystem B₁ B₂).zetaSeriesC s = B₁.zetaSeriesC s * B₂.zetaSeriesC s := by
  have hn : ∀ (B : BeurlingSystem) (g : B.Integer),
      ‖((B.intNorm g : ℝ) : ℂ) ^ (-s)‖ = (B.intNorm g) ^ (-s.re) := fun B g => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (B.intNorm_pos g), Complex.neg_re]
  have hn₁ : Summable fun u : B₁.Integer => ‖((B₁.intNorm u : ℝ) : ℂ) ^ (-s)‖ := by
    simpa only [hn] using h₁
  have hn₂ : Summable fun v : B₂.Integer => ‖((B₂.intNorm v : ℝ) : ℂ) ^ (-s)‖ := by
    simpa only [hn] using h₂
  have hre := (joinEquiv (α := B₁.Label) (γ := B₂.Label)).tsum_eq
    (fun g : Multiset (B₁.Label ⊕ B₂.Label) => (((sumSystem B₁ B₂).intNorm g : ℝ) : ℂ) ^ (-s))
  unfold BeurlingSystem.zetaSeriesC
  rw [tsum_mul_tsum_of_summable_norm hn₁ hn₂]
  refine hre.symm.trans (tsum_congr fun ⟨u, v⟩ => ?_)
  show (((sumSystem B₁ B₂).intNorm (joinEquiv (u, v)) : ℝ) : ℂ) ^ (-s) = _
  rw [intNorm_joinEquiv_sumSystem, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (B₁.intNorm_pos u).le (B₂.intNorm_pos v).le]

/-- **Thin additions keep the count rate.** -/
theorem sumSystem_count_sub_le {B₁ B₂ : BeurlingSystem} (hd₁ : B₁.IsDiscrete)
    (hd₂ : B₂.IsDiscrete) {A₁ C₁ β : ℝ} (hA₁ : 0 ≤ A₁) (hC₁ : 0 ≤ C₁) (hβ1 : β ≤ 1)
    (h₁ : ∀ y : ℝ, 1 ≤ y → |(B₁.countBall y : ℝ) - A₁ * y| ≤ C₁ * y ^ β)
    (hZ : Summable fun v : B₂.Integer => (B₂.intNorm v) ^ (-β)) {x : ℝ} (hx : 1 ≤ x) :
    |((sumSystem B₁ B₂).countBall x : ℝ) -
        A₁ * (∑' v : B₂.Integer, (B₂.intNorm v) ^ (-(1 : ℝ))) * x| ≤
      (C₁ + A₁) * (∑' v : B₂.Integer, (B₂.intNorm v) ^ (-β)) * x ^ β := by
  classical
  have hx0 : 0 < x := by linarith
  set T := (hd₂ x).toFinset with hT
  set Z : ℝ := ∑' v : B₂.Integer, (B₂.intNorm v) ^ (-β) with hZdef
  have hnn : ∀ (e : ℝ) (v : B₂.Integer), 0 ≤ (B₂.intNorm v) ^ e :=
    fun e v => Real.rpow_nonneg (B₂.intNorm_pos v).le e
  have hle1 : ∀ v : B₂.Integer, (B₂.intNorm v) ^ (-(1 : ℝ)) ≤ (B₂.intNorm v) ^ (-β) := fun v =>
    Real.rpow_le_rpow_of_exponent_le (B₂.one_le_intNorm v) (by linarith)
  have hZ1 : Summable fun v : B₂.Integer => (B₂.intNorm v) ^ (-(1 : ℝ)) :=
    Summable.of_nonneg_of_le (hnn _) hle1 hZ
  set Z₁ : ℝ := ∑' v : B₂.Integer, (B₂.intNorm v) ^ (-(1 : ℝ)) with hZ1def
  have hmemT : ∀ v : B₂.Integer, v ∈ T ↔ B₂.intNorm v ≤ x := fun v => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  have hTZ : ∑ v ∈ T, (B₂.intNorm v) ^ (-β) ≤ Z := hZ.sum_le_tsum T fun v _ => hnn _ v
  -- the integers of `B₂` below `x`
  have hmain : |∑ v ∈ T, ((B₁.countBall (x / B₂.intNorm v) : ℝ) - A₁ * (x / B₂.intNorm v))| ≤
      C₁ * Z * x ^ β := by
    calc |∑ v ∈ T, ((B₁.countBall (x / B₂.intNorm v) : ℝ) - A₁ * (x / B₂.intNorm v))|
        ≤ ∑ v ∈ T, |(B₁.countBall (x / B₂.intNorm v) : ℝ) - A₁ * (x / B₂.intNorm v)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ T, C₁ * (x ^ β * (B₂.intNorm v) ^ (-β)) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hv0 := B₂.intNorm_pos v
          have h := h₁ (x / B₂.intNorm v) ((one_le_div hv0).mpr ((hmemT v).mp hv))
          rwa [Real.div_rpow hx0.le hv0.le, div_eq_mul_inv (x ^ β), ← Real.rpow_neg hv0.le] at h
      _ = C₁ * x ^ β * ∑ v ∈ T, (B₂.intNorm v) ^ (-β) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ C₁ * x ^ β * Z :=
          mul_le_mul_of_nonneg_left hTZ (mul_nonneg hC₁ (Real.rpow_nonneg hx0.le _))
      _ = C₁ * Z * x ^ β := by ring
  -- the integers of `B₂` above `x`
  have htail0 : ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ)) ≤ Z₁ :=
    hZ1.sum_le_tsum T fun v _ => hnn _ v
  have htail : Z₁ ≤ ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ)) + x ^ (β - 1) * Z := by
    have hfin : Summable fun v : B₂.Integer =>
        if v ∈ T then (B₂.intNorm v) ^ (-(1 : ℝ)) else 0 :=
      summable_of_ne_finset_zero (s := T) fun v hv => if_neg hv
    have hpt : ∀ v : B₂.Integer, (B₂.intNorm v) ^ (-(1 : ℝ)) ≤
        (if v ∈ T then (B₂.intNorm v) ^ (-(1 : ℝ)) else 0) +
          x ^ (β - 1) * (B₂.intNorm v) ^ (-β) := by
      intro v
      have hv0 := B₂.intNorm_pos v
      by_cases hv : v ∈ T
      · rw [if_pos hv]
        have h0 : 0 ≤ x ^ (β - 1) * (B₂.intNorm v) ^ (-β) :=
          mul_nonneg (Real.rpow_nonneg hx0.le _) (hnn _ v)
        linarith
      · rw [if_neg hv, zero_add]
        have hxv : x ≤ B₂.intNorm v := le_of_lt (lt_of_not_ge fun h => hv ((hmemT v).mpr h))
        have h1 : (B₂.intNorm v) ^ (-(1 : ℝ)) =
            (B₂.intNorm v) ^ (β - 1) * (B₂.intNorm v) ^ (-β) := by
          rw [← Real.rpow_add hv0]; congr 1; ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hx0 hxv (by linarith)) (hnn _ v)
    calc Z₁ ≤ ∑' v : B₂.Integer, ((if v ∈ T then (B₂.intNorm v) ^ (-(1 : ℝ)) else 0) +
          x ^ (β - 1) * (B₂.intNorm v) ^ (-β)) :=
          hZ1.tsum_le_tsum hpt (hfin.add (hZ.mul_left _))
      _ = ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ)) + x ^ (β - 1) * Z := by
          rw [hfin.tsum_add (hZ.mul_left _), tsum_mul_left,
            tsum_eq_sum (s := T) (fun v hv => if_neg hv)]
          congr 1
          exact Finset.sum_congr rfl fun v hv => if_pos hv
  -- assembly
  have hcount : ((sumSystem B₁ B₂).countBall x : ℝ) =
      ∑ v ∈ T, (B₁.countBall (x / B₂.intNorm v) : ℝ) := by
    rw [countBall_sumSystem hd₁ hd₂ x, Nat.cast_sum]
  have hdecomp : ((sumSystem B₁ B₂).countBall x : ℝ) - A₁ * Z₁ * x =
      ∑ v ∈ T, ((B₁.countBall (x / B₂.intNorm v) : ℝ) - A₁ * (x / B₂.intNorm v)) -
        A₁ * x * (Z₁ - ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ))) := by
    have hlin : ∑ v ∈ T, A₁ * (x / B₂.intNorm v) =
        A₁ * x * ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Real.rpow_neg_one]; ring
    rw [hcount, Finset.sum_sub_distrib, hlin]
    ring
  have hxβ : x * x ^ (β - 1) = x ^ β := by
    rw [Real.rpow_sub_one hx0.ne']; field_simp
  have ht1 : 0 ≤ A₁ * x * (Z₁ - ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ))) :=
    mul_nonneg (mul_nonneg hA₁ hx0.le) (by linarith)
  have ht2 : A₁ * x * (Z₁ - ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ))) ≤ A₁ * Z * x ^ β := by
    calc A₁ * x * (Z₁ - ∑ v ∈ T, (B₂.intNorm v) ^ (-(1 : ℝ)))
        ≤ A₁ * x * (x ^ (β - 1) * Z) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA₁ hx0.le)
      _ = A₁ * Z * (x * x ^ (β - 1)) := by ring
      _ = A₁ * Z * x ^ β := by rw [hxβ]
  rw [hdecomp]
  rw [abs_le] at hmain ⊢
  constructor <;> linarith [hmain.1, hmain.2]

/-! ## Integers supported on a thin set of primes -/

theorem sFreeR_one (S : Set ℕ) : sFreeR S 1 = 1 := by
  unfold sFreeR SFree
  rw [if_pos ⟨one_ne_zero, by simp⟩]

theorem sFreeR_mul (S : Set ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    sFreeR S (m * n) = sFreeR S m * sFreeR S n := by
  classical
  have hiff : SFree S (m * n) ↔ SFree S m ∧ SFree S n := by
    unfold SFree
    rw [Nat.primeFactors_mul hm hn]
    simp only [ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
      Finset.mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨h1, h2⟩ p (hp | hp)
      · exact h1 p hp
      · exact h2 p hp
  unfold sFreeR
  by_cases h1 : SFree S m <;> by_cases h2 : SFree S n <;> simp [hiff, h1, h2]

open Classical in
theorem sFreeR_prime (S : Set ℕ) {p : ℕ} (hp : p.Prime) :
    sFreeR S p = if p ∈ S then 0 else 1 := by
  unfold sFreeR SFree
  rw [hp.primeFactors]
  by_cases h : p ∈ S
  · rw [if_pos h, if_neg (by simp [h])]
  · rw [if_neg h, if_pos ⟨hp.ne_zero, by simpa using h⟩]

/-- **Integers supported on a thin set of primes.**  If `Σ_{p ∈ T} p^{−β} < ∞`, `β > 0`, the
integers all of whose prime factors lie in `T` are summable at the exponent `β`. -/
theorem summable_sFreeR_compl_rpow {T : Set ℕ} {β : ℝ} (hβ : 0 < β)
    (hT : Summable fun p : ℕ => T.indicator (fun n => (n : ℝ) ^ (-β)) p) :
    Summable fun n : ℕ => sFreeR Tᶜ n * (n : ℝ) ^ (-β) := by
  classical
  -- the completely multiplicative weight
  let f : ℕ →* ℝ :=
    { toFun := fun n => sFreeR Tᶜ n * (n : ℝ) ^ (-β)
      map_one' := by simp [sFreeR_one]
      map_mul' := fun m n => by
        rcases eq_or_ne m 0 with rfl | hm
        · simp [sFreeR_zero]
        rcases eq_or_ne n 0 with rfl | hn
        · simp [sFreeR_zero]
        rw [sFreeR_mul _ hm hn, Nat.cast_mul,
          Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
        ring }
  have hfdef : ∀ n : ℕ, f n = sFreeR Tᶜ n * (n : ℝ) ^ (-β) := fun n => rfl
  have hf0 : f 0 = 0 := by rw [hfdef, sFreeR_zero, zero_mul]
  have hfnn : ∀ n : ℕ, 0 ≤ f n := fun n => by
    rw [hfdef]
    exact mul_nonneg (sFreeR_nonneg _ n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  set q : ℝ := (2 : ℝ) ^ (-β) with hq
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1q : 0 < 1 - q := by linarith
  have hfp : ∀ p : ℕ, p.Prime → f p = T.indicator (fun n => (n : ℝ) ^ (-β)) p := by
    intro p hp
    rw [hfdef, sFreeR_prime _ hp]
    by_cases h : p ∈ T
    · rw [if_neg (show ¬ p ∈ Tᶜ from fun hc => hc h), Set.indicator_of_mem h, one_mul]
    · rw [if_pos (show p ∈ Tᶜ from h), Set.indicator_of_notMem h, zero_mul]
  have hfpq : ∀ p : ℕ, p.Prime → f p ≤ q := by
    intro p hp
    have hpow : (p : ℝ) ^ (-β) ≤ q :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
    have hpos : 0 ≤ (p : ℝ) ^ (-β) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    rw [hfp p hp]
    by_cases h : p ∈ T
    · rw [Set.indicator_of_mem h]; exact hpow
    · rw [Set.indicator_of_notMem h]; exact hpos.trans hpow
  have hlt : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := fun {p} hp => by
    rw [Real.norm_of_nonneg (hfnn p)]
    exact lt_of_le_of_lt (hfpq p hp) hq1
  set Z : ℝ := ∑' p : ℕ, T.indicator (fun n => (n : ℝ) ^ (-β)) p with hZ
  -- the Euler products are bounded
  have hprod : ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ ≤ Real.exp (Z / (1 - q)) := by
    intro N
    have hstep : ∀ p ∈ N.primesBelow, (1 - f p)⁻¹ ≤ Real.exp (f p / (1 - q)) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesBelow hp
      have hx0 := hfnn p
      have hxq := hfpq p hpp
      have h1x : 0 < 1 - f p := by linarith
      have hy : 0 ≤ f p / (1 - q) := div_nonneg hx0 h1q.le
      have hyq : f p / (1 - q) * (1 - q) = f p := div_mul_cancel₀ _ h1q.ne'
      have key : (1 - f p)⁻¹ ≤ 1 + f p / (1 - q) := by
        rw [inv_eq_one_div, div_le_iff₀ h1x]
        nlinarith [mul_nonneg hy (sub_nonneg.mpr hxq)]
      linarith [Real.add_one_le_exp (f p / (1 - q))]
    calc ∏ p ∈ N.primesBelow, (1 - f p)⁻¹
        ≤ ∏ p ∈ N.primesBelow, Real.exp (f p / (1 - q)) :=
          Finset.prod_le_prod (fun p hp => inv_nonneg.mpr (by
            linarith [hfpq p (Nat.prime_of_mem_primesBelow hp)])) hstep
      _ = Real.exp (∑ p ∈ N.primesBelow, f p / (1 - q)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (Z / (1 - q)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← Finset.sum_div, div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr h1q.le)
          calc ∑ p ∈ N.primesBelow, f p
              = ∑ p ∈ N.primesBelow, T.indicator (fun n => (n : ℝ) ^ (-β)) p :=
                Finset.sum_congr rfl fun p hp => hfp p (Nat.prime_of_mem_primesBelow hp)
            _ ≤ Z := hT.sum_le_tsum _ fun p _ =>
                Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) p
  -- every partial sum is at most an Euler product
  refine summable_of_sum_range_le (c := Real.exp (Z / (1 - q))) hfnn fun N => ?_
  obtain ⟨hsum, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric (f := f) hlt N
  have hind : Summable ((N.smoothNumbers : Set ℕ).indicator f) :=
    summable_subtype_iff_indicator.mp hsum.of_norm
  calc ∑ n ∈ range N, f n
      = ∑ n ∈ range N, (N.smoothNumbers : Set ℕ).indicator f n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · rw [hf0, Set.indicator_apply]
          split_ifs <;> simp [hf0]
        · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hpos (Finset.mem_range.mp hn))]
    _ ≤ ∑' n, (N.smoothNumbers : Set ℕ).indicator f n :=
        hind.sum_le_tsum _ fun n _ => Set.indicator_nonneg (fun m _ => hfnn m) n
    _ = ∑' m : N.smoothNumbers, f m := (_root_.tsum_subtype _ f).symm
    _ = ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ := hhas.tsum_eq
    _ ≤ Real.exp (Z / (1 - q)) := hprod N

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.ThinAdditions
