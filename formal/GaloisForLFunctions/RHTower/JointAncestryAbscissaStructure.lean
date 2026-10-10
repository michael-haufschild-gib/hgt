import GaloisForLFunctions.RHTower.JointAncestryUndressedPositivity
import GaloisForLFunctions.RHTower.WeilLagFunctionDense

/-!
# The JAS positivity abscissa: a closed ray in `[0, ∞)`

Let `σ* = inf {σ : N_σ is positive semidefinite}`.

* **No positivity below `0`.**  For the characters `(k+1)/k` the lag `log(k/(k+1))` tends to `0` while
  the size `log k(k+1)` tends to infinity, so for `σ < 0` the coefficients
  `(k(k+1))^{-σ} Φ(log(k/(k+1)))` exceed `Φ(0)`, violating the `2 × 2` minor.
* **Closedness.**  Positivity at every `σ' > σ` passes to `σ` by continuity of the finitely many
  coefficients involved.

Hence the positive dressings form the closed ray `[σ*, ∞)` with `0 ≤ σ*`, and:

* `σ* = 0` iff RH;
* a maximal off-line zero at distance `δ₀` forces `σ* ≥ 1 + δ₀`.

So, apart from an off-line zero set without a largest distance, `σ*` never lies in `(0, 1]`.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## Characters of reduced fractions -/

theorem jasNatChar_apply_eq_zero_of_coprime {a b : ℕ} (h : Nat.Coprime a b) (p : Nat.Primes) :
    jasNatChar a p = 0 ∨ jasNatChar b p = 0 := by
  rw [jasNatChar_apply, jasNatChar_apply]
  by_cases ha : (p : ℕ) ∣ a
  · right
    have hb : ¬ (p : ℕ) ∣ b := fun hb => by
      have := Nat.dvd_gcd ha hb
      rw [Nat.Coprime.gcd_eq_one h] at this
      exact Nat.Prime.not_dvd_one p.2 this
    simp [Nat.factorization_eq_zero_of_not_dvd hb]
  · left
    simp [Nat.factorization_eq_zero_of_not_dvd ha]

theorem jasLogPos_sub_jasNatChar {a b : ℕ} (ha : a ≠ 0) (h : Nat.Coprime a b) :
    jasLogPos (jasNatChar a - jasNatChar b) = Real.log a := by
  rw [← jasLogPos_jasNatChar ha]
  unfold jasLogPos
  set S := (jasNatChar a).support ∪ (jasNatChar b).support
  rw [Finsupp.sum_of_support_subset _ (s := S) (fun p hp => by
      rw [Finsupp.mem_support_iff, Finsupp.sub_apply] at hp
      rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      by_contra hc
      push Not at hc
      rw [hc.1, hc.2, sub_zero] at hp
      exact hp rfl) _ (by simp),
    Finsupp.sum_of_support_subset _ (s := S) Finset.subset_union_left _ (by simp)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sub_apply]
  rcases jasNatChar_apply_eq_zero_of_coprime h p with h0 | h0
  · have hb : 0 ≤ jasNatChar b p := by rw [jasNatChar_apply]; positivity
    rw [h0, zero_sub, show (-(jasNatChar b p)).toNat = 0 by omega]
    simp
  · rw [h0, sub_zero]

theorem jasLogNeg_sub_jasNatChar {a b : ℕ} (hb : b ≠ 0) (h : Nat.Coprime a b) :
    jasLogNeg (jasNatChar a - jasNatChar b) = Real.log b := by
  have h1 : jasLogNeg (jasNatChar a - jasNatChar b) = jasLogPos (jasNatChar b - jasNatChar a) := by
    unfold jasLogNeg jasLogPos
    rw [show jasNatChar a - jasNatChar b = -(jasNatChar b - jasNatChar a) by abel,
      Finsupp.sum_neg_index (by simp)]
    simp
  rw [h1, jasLogPos_sub_jasNatChar hb h.symm]

/-! ## No positivity below `σ = 0` -/

/-- Positivity bounds coefficients from below as well: `Re N_σ(m) ≥ -N_σ(0)`. -/
theorem neg_le_re_jasDressedLagAggregate_of_psd {σ : ℝ} (h : JasDressedPSD σ)
    {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0) :
    -poleSharpConstant ≤ (jasDressedLagAggregate σ m).re := by
  have hinj : Set.InjOn (![0, m] : Fin 2 → Nat.Primes →₀ ℤ) (Finset.univ : Finset (Fin 2)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hform := h (Fin 2) Finset.univ ![1, 1] ![0, m] hinj
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_sub,
    sub_zero, jasDressedLagAggregate_neg, jasDressedLagAggregate_zero, map_one,
    Complex.add_re, Complex.mul_re] at hform
  simp at hform
  linarith

/-- **No positivity below `σ = 0`.** -/
theorem not_jasDressedPSD_of_neg {σ : ℝ} (hσ : σ < 0) : ¬ JasDressedPSD σ := by
  intro h
  have hΦ0 : 0 < poleSharpConstant := poleSharpConstant_pos
  -- the lag of `(k+1)/k`
  have hL : Tendsto (fun k : ℕ => Real.log k - Real.log (k + 1 : ℕ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) / (k + 1 : ℕ))) atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => (k : ℝ) / (k + 1 : ℕ)) atTop (𝓝 1) := by
        have := tendsto_natCast_div_add_atTop (1 : ℝ)
        simpa using this
      simpa using this.log one_ne_zero
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Real.log_div (by exact_mod_cast (show k ≠ 0 by omega)) (by positivity)]
  have hΦ : Tendsto (fun k : ℕ => weilLagFunctionReal (Real.log k - Real.log (k + 1 : ℕ))) atTop
      (𝓝 poleSharpConstant) := by
    have hc := continuous_weilLagFunctionReal.tendsto 0
    have h0 : weilLagFunctionReal 0 = poleSharpConstant := by
      rw [weilLagFunctionReal, weilLagFunction_zero, Complex.ofReal_re]
    rw [h0] at hc
    exact hc.comp hL
  have hexp : Tendsto (fun k : ℕ => Real.exp (-σ * (Real.log (k + 1 : ℕ) + Real.log k))) atTop
      atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    refine Tendsto.const_mul_atTop (by linarith) ?_
    refine Tendsto.atTop_add_atTop (Real.tendsto_log_atTop.comp ?_) (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨k, hk1, hkΦ, hkexp⟩ := ((eventually_ge_atTop 1).and
    ((hΦ.eventually (lt_mem_nhds (show poleSharpConstant / 2 < poleSharpConstant by linarith))).and
      (hexp.eventually_gt_atTop 2))).exists
  have hcop : Nat.Coprime (k + 1) k := by simp
  have hk0 : k ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = jasNatChar (k + 1) - jasNatChar k := ⟨_, rfl⟩
  have hpos : jasLogPos m = Real.log (k + 1 : ℕ) := by
    rw [hm]; exact jasLogPos_sub_jasNatChar (show k + 1 ≠ 0 by omega) hcop
  have hneg : jasLogNeg m = Real.log k := by
    rw [hm]; exact jasLogNeg_sub_jasNatChar hk0 hcop
  have hm0 : m ≠ 0 := by
    intro h0
    have h1 : jasLogPos m = 0 := by rw [h0]; simp [jasLogPos]
    have h2 : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
    linarith
  have hval : jasDressedLagAggregate σ m =
      (Real.exp (-σ * (Real.log (k + 1 : ℕ) + Real.log k)) : ℂ) *
        (weilLagFunctionReal (Real.log k - Real.log (k + 1 : ℕ)) : ℂ) := by
    rw [jasDressedLagAggregate, jasLogSize, hpos, hneg, weilLagFunction_eq_ofReal]
  have hle := re_jasDressedLagAggregate_le_of_psd h hm0
  rw [hval, ← Complex.ofReal_mul, Complex.ofReal_re] at hle
  have : 2 * (poleSharpConstant / 2) < Real.exp (-σ * (Real.log (k + 1 : ℕ) + Real.log k)) *
      weilLagFunctionReal (Real.log k - Real.log (k + 1 : ℕ)) := by
    have h1 : 0 < poleSharpConstant / 2 := by linarith
    calc 2 * (poleSharpConstant / 2) < Real.exp (-σ * (Real.log (k + 1 : ℕ) + Real.log k)) *
          (poleSharpConstant / 2) := mul_lt_mul_of_pos_right hkexp h1
      _ ≤ _ := mul_le_mul_of_nonneg_left hkΦ.le (Real.exp_pos _).le
  linarith

/-! ## Closedness and the abscissa -/

theorem continuous_jasDressedLagAggregate (m : Nat.Primes →₀ ℤ) :
    Continuous fun σ : ℝ => jasDressedLagAggregate σ m := by
  unfold jasDressedLagAggregate
  fun_prop

/-- **Closedness.**  Positivity at every `σ' > σ` implies positivity at `σ`. -/
theorem jasDressedPSD_of_forall_gt {σ : ℝ} (h : ∀ σ' > σ, JasDressedPSD σ') : JasDressedPSD σ := by
  intro ι t c n hinj
  have hcont : Continuous fun σ' : ℝ =>
      (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ' (n i - n j)).re := by
    refine Complex.continuous_re.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul (continuous_jasDressedLagAggregate _)
  have ht := (hcont.tendsto σ).mono_left (nhdsWithin_le_nhds (s := Set.Ioi σ))
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun σ' hσ' => h σ' hσ' ι t c n hinj)

/-- The JAS positivity abscissa `σ* = inf {σ : N_σ ⪰ 0}`. -/
def jasAbscissa : ℝ := sInf {σ : ℝ | JasDressedPSD σ}

theorem jasPSD_set_nonempty : {σ : ℝ | JasDressedPSD σ}.Nonempty := by
  obtain ⟨σ₀, h⟩ := exists_jasDressedPSD
  exact ⟨σ₀, h σ₀ le_rfl⟩

theorem jasPSD_set_bddBelow : BddBelow {σ : ℝ | JasDressedPSD σ} :=
  ⟨0, fun _ hσ => le_of_not_gt fun h => not_jasDressedPSD_of_neg h hσ⟩

/-- **`σ* ≥ 0` unconditionally.** -/
theorem zero_le_jasAbscissa : 0 ≤ jasAbscissa :=
  le_csInf jasPSD_set_nonempty fun _ hσ => le_of_not_gt fun h => not_jasDressedPSD_of_neg h hσ

/-- The abscissa is attained. -/
theorem jasDressedPSD_jasAbscissa : JasDressedPSD jasAbscissa := by
  refine jasDressedPSD_of_forall_gt fun σ' hσ' => ?_
  obtain ⟨σ'', hσ'', hlt⟩ := exists_lt_of_csInf_lt jasPSD_set_nonempty hσ'
  exact JasDressedPSD.mono hσ'' hlt.le

/-- **The positive dressings are exactly the ray `[σ*, ∞)`.** -/
theorem jasDressedPSD_iff_jasAbscissa_le {σ : ℝ} : JasDressedPSD σ ↔ jasAbscissa ≤ σ :=
  ⟨fun h => csInf_le jasPSD_set_bddBelow h, fun h => jasDressedPSD_jasAbscissa.mono h⟩

/-- **RH ⟺ `σ* = 0`.** -/
theorem riemannHypothesis_iff_jasAbscissa_eq_zero : RiemannHypothesis ↔ jasAbscissa = 0 := by
  constructor
  · intro h
    exact le_antisymm (jasDressedPSD_iff_jasAbscissa_le.mp
      (jasDressedPSD_zero_of_riemannHypothesis h)) zero_le_jasAbscissa
  · intro h
    exact riemannHypothesis_of_jasDressedPSD_zero (jasDressedPSD_iff_jasAbscissa_le.mpr h.le)

/-- A maximal off-line zero at distance `δ₀` forces `σ* ≥ 1 + δ₀`. -/
theorem le_jasAbscissa_of_maximal_offLine (q₀ : XiZeroCopy) (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) :
    1 + |(q₀.1 : ℂ).re - 1 / 2| ≤ jasAbscissa :=
  le_of_not_gt fun h => not_jasDressedPSD_of_maximal_offLine q₀ hoff hmax h jasDressedPSD_jasAbscissa

/-- Off-line Xi zeros exist and every one of them is exceeded in distance from the critical line by
another Xi zero. -/
def JasOffLineChain : Prop :=
  (∃ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2) ∧
    ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
      ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2|

/-- **The abscissa gap.**  If `σ* ≤ 1` then either `σ* = 0` (RH), or the off-line zeros form a chain
without a largest distance from the critical line. -/
theorem jasAbscissa_eq_zero_or_chain (h : jasAbscissa ≤ 1) : jasAbscissa = 0 ∨ JasOffLineChain := by
  rcases riemannHypothesis_or_offLine_chain_of_jasDressedPSD h jasDressedPSD_jasAbscissa with
    hRH | hchain
  · exact Or.inl (riemannHypothesis_iff_jasAbscissa_eq_zero.mp hRH)
  · by_cases hRH : RiemannHypothesis
    · exact Or.inl (riemannHypothesis_iff_jasAbscissa_eq_zero.mp hRH)
    · obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
      exact Or.inr ⟨⟨q, ne_of_gt hq⟩, hchain⟩

end

end RHTower
