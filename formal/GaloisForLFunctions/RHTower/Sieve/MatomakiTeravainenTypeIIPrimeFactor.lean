import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenUniformDivisorBound
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPerronFactorization
import GaloisForLFunctions.RHTower.Sieve.ShortPrimeBlockTwistDecay

/-!
# The short Type-II factor on the one-line

The (2.11) factor `M₁(s) = ∑ α_m m^{-s}` of a Proposition 2.2(iii) piece is the product of its prime
block sums `∏_i ∑_{Q_i < q ≤ Q_i(1+δ)} q^{-s}`.  Each block sum is at most `1` in absolute value on
`Re s = 1`, and at the paper scale one of them is `≤ exp(-(log X)^{1/30})` for
`exp(c√log X) ≤ |t| ≤ 4X` (`ShortPrimeBlockTwistDecay`).  This is (5.6) of Matomäki–Teräväinen.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

noncomputable section

theorem natCast_finset_prod_cpow {ι : Type*} (s : Finset ι) (f : ι → ℕ) (z : ℂ) :
    (((∏ i ∈ s, f i : ℕ) : ℂ)) ^ z = ∏ i ∈ s, ((f i : ℕ) : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, Nat.cast_mul,
      ← Complex.natCast_mul_natCast_cpow]

/-- The Dirichlet polynomial of the (2.11) coefficient is the product of its block sums. -/
theorem sum_typeIIPrimeCoefficient_mul_cpow_eq_prod (I : Finset ℕ) (block : ℕ → Finset ℕ)
    (S : Finset ℕ)
    (hS : ∀ q : I → ℕ, (∀ i : I, q i ∈ block i) → ∏ i, q i ∈ S) (z : ℂ) :
    ∑ m ∈ S, mtTypeIIPrimeCoefficient I block m * (m : ℂ) ^ z =
      ∏ i ∈ I, ∑ q ∈ block i, (q : ℂ) ^ z := by
  classical
  rw [← Finset.prod_coe_sort I, Finset.prod_univ_sum]
  have h1 : ∀ q ∈ Fintype.piFinset (fun i : I => block i),
      ∏ i, ((q i : ℕ) : ℂ) ^ z = (((∏ i, q i : ℕ) : ℂ)) ^ z :=
    fun q _ => (natCast_finset_prod_cpow _ q z).symm
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun q : I → ℕ => ∏ i, q i) (t := S)
    (fun q hq => hS q (Fintype.mem_piFinset.1 hq))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.1 hq).2]]
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The short Type-II factor on the line `Re s = σ`. -/
def mtTypeIIPrimeFactor {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (σ t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF (mtTypeIIPrimeCoefficient data.indices data.block)
      data.M₁ ((1 + δ) ^ data.indices.card * data.M₁) n)
    ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ σ t

/-- **The short factor is the product of its block sums.** -/
theorem mtTypeIIPrimeFactor_eq_prod {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (σ t : ℝ) :
    mtTypeIIPrimeFactor data σ t =
      ∏ i ∈ data.indices, ∑ q ∈ data.block i, (q : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * Complex.I)) := by
  classical
  unfold mtTypeIIPrimeFactor perronPoly
  rw [data.primeIntervalAF_eq_coefficientAF]
  have hsum : ∑ n ∈ Finset.Icc 1 ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊,
      mtCoefficientAF (mtTypeIIPrimeCoefficient data.indices data.block) n *
        (n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * Complex.I)) =
      ∑ n ∈ Finset.Icc 1 ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊,
        mtTypeIIPrimeCoefficient data.indices data.block n *
          (n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * Complex.I)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [mtCoefficientAF_apply_of_pos _ (by have := (Finset.mem_Icc.1 hn).1; omega)]
  rw [hsum]
  refine sum_typeIIPrimeCoefficient_mul_cpow_eq_prod _ _ _ (fun q hq => ?_) _
  have hne : mtTypeIIPrimeCoefficient data.indices data.block (∏ i, q i) ≠ 0 := by
    rw [mtTypeIIPrimeCoefficient, Nat.cast_ne_zero]
    exact (Finset.card_pos.2 ⟨q, mem_mtTypeIIPrimeTuples.2 ⟨hq, rfl⟩⟩).ne'
  have hsupp := data.primeCoefficient_support hne
  have hM₁ : 0 < data.M₁ := by
    rw [data.M₁_eq]
    exact Finset.prod_pos fun i _ => data.z₀_pos.trans_le (data.Q_mem i i.2).1
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · have : (0 : ℝ) < ((∏ i, q i : ℕ) : ℝ) := hM₁.trans hsupp.1
    exact_mod_cast this
  · exact_mod_cast hsupp.2.trans (Nat.le_ceil _)

/-- A block of primes in `(Q, Q(1+δ)]` has harmonic mass at most `δ + 1/Q`. -/
theorem sum_one_div_le_of_mem_block {B : Finset ℕ} {Q δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 ≤ δ)
    (hB : ∀ p ∈ B, Q < p ∧ (p : ℝ) ≤ Q * (1 + δ)) :
    ∑ p ∈ B, (1 : ℝ) / p ≤ δ + 1 / Q := by
  have hQ0 : 0 < Q := by linarith
  have hsub : B ⊆ Finset.Ioc ⌊Q⌋₊ ⌊Q * (1 + δ)⌋₊ := by
    intro p hp
    obtain ⟨h1, h2⟩ := hB p hp
    exact Finset.mem_Ioc.2 ⟨(Nat.floor_lt hQ0.le).2 h1, Nat.le_floor h2⟩
  have hcard : (B.card : ℝ) ≤ Q * δ + 1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at h
    have h1 : ((⌊Q * (1 + δ)⌋₊ - ⌊Q⌋₊ : ℕ) : ℝ) ≤ Q * δ + 1 := by
      rcases le_total ⌊Q * (1 + δ)⌋₊ ⌊Q⌋₊ with hle | hle
      · rw [Nat.sub_eq_zero_of_le hle]; push_cast; nlinarith
      · rw [Nat.cast_sub hle]
        have ha := Nat.floor_le (by positivity : (0 : ℝ) ≤ Q * (1 + δ))
        have hb := Nat.lt_floor_add_one Q
        linarith
    exact (Nat.cast_le.2 h).trans h1
  calc ∑ p ∈ B, (1 : ℝ) / p ≤ ∑ _p ∈ B, 1 / Q := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact one_div_le_one_div_of_le hQ0 (hB p hp).1.le
    _ = B.card * (1 / Q) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q * δ + 1) * (1 / Q) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = δ + 1 / Q := by field_simp

theorem norm_natCast_cpow_one_add_mul_I {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖(q : ℂ) ^ (-((1 : ℝ) + (t : ℝ) * Complex.I))‖ = 1 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp [Real.rpow_neg_one]

/-- On `Re s = 1` every block sum of a Type-II datum has absolute value at most one. -/
theorem norm_sum_block_cpow_le_one {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hz₀ : 2 ≤ z₀) (hδ : δ ≤ 1 / 2) {i : ℕ} (hi : i ∈ data.indices) (t : ℝ) :
    ‖∑ q ∈ data.block i, (q : ℂ) ^ (-((1 : ℝ) + (t : ℝ) * Complex.I))‖ ≤ 1 := by
  have hQ := data.Q_mem i hi
  have hQ2 : 2 ≤ data.Q i := hz₀.trans hQ.1
  refine (norm_sum_le _ _).trans ?_
  have hmem : ∀ p ∈ data.block i, data.Q i < p ∧ (p : ℝ) ≤ data.Q i * (1 + δ) := fun p hp =>
    ⟨((data.block_eq i hi p).1 hp).2.1, ((data.block_eq i hi p).1 hp).2.2⟩
  calc ∑ q ∈ data.block i, ‖(q : ℂ) ^ (-((1 : ℝ) + (t : ℝ) * Complex.I))‖
      = ∑ q ∈ data.block i, (1 : ℝ) / q := by
        refine Finset.sum_congr rfl fun q hq => ?_
        exact norm_natCast_cpow_one_add_mul_I ((data.block_eq i hi q).1 hq).1.pos t
    _ ≤ δ + 1 / data.Q i :=
        sum_one_div_le_of_mem_block (by linarith) data.δ_nonneg hmem
    _ ≤ 1 := by
        have : 1 / data.Q i ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hQ2
        linarith

/-- On `Re s = 1` the short Type-II factor has absolute value at most one. -/
theorem norm_mtTypeIIPrimeFactor_le_one {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hz₀ : 2 ≤ z₀) (hδ : δ ≤ 1 / 2) (t : ℝ) :
    ‖mtTypeIIPrimeFactor data 1 t‖ ≤ 1 := by
  rw [mtTypeIIPrimeFactor_eq_prod, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun i hi => norm_sum_block_cpow_le_one data hz₀ hδ hi t

/-- **(5.6) at the paper scale.** -/
theorem eventually_norm_mtTypeIIPrimeFactor_le {c : ℝ} (hc : 0 < c) {A : ℕ} (hA : 1 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ {Y z ε : ℝ}
      (data : MTTypeIIPieceData X Y (mtLowerCutoff X) z (mtPaperWidth A X) ε) (t : ℝ),
      z ≤ X → Real.exp (c * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ |t| → |t| ≤ 4 * X →
      ‖mtTypeIIPrimeFactor data 1 t‖ ≤ Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)) := by
  have hcut : ∀ᶠ X : ℝ in atTop, 2 ≤ mtLowerCutoff X := by
    filter_upwards [tendsto_mtLowerLogCutoff_atTop.eventually_ge_atTop 1] with X hX
    rw [mtLowerCutoff]
    have := Real.add_one_le_exp (mtLowerLogCutoff X)
    linarith
  have hwidth : ∀ᶠ X : ℝ in atTop, mtPaperWidth A X ≤ 1 / 2 := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2] with X hX
    rw [mtPaperWidth, Real.rpow_neg (by linarith), Real.rpow_natCast]
    have h1 : (2 : ℝ) ≤ Real.log X ^ (10 * A) := by
      calc (2 : ℝ) ≤ Real.log X := hX
        _ = Real.log X ^ 1 := (pow_one _).symm
        _ ≤ Real.log X ^ (10 * A) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  filter_upwards [eventually_norm_sum_primeBlock_cpow_le hc, hcut, hwidth] with X hblock hz2 hw
  intro Y z ε data t hzX ht1 ht2
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.1 data.R_pos
  rw [mtTypeIIPrimeFactor_eq_prod, norm_prod, ← Finset.mul_prod_erase _ _ hi₀]
  have hQ := data.Q_mem i₀ hi₀
  have h1 := hblock (data.block i₀) (data.Q i₀) (mtPaperWidth A X) t hQ.1
    (hQ.2.le.trans hzX) data.δ_nonneg (by linarith) (data.block_eq i₀ hi₀) ht1 ht2
  have hrest : ∏ i ∈ data.indices.erase i₀,
      ‖∑ q ∈ data.block i, (q : ℂ) ^ (-((1 : ℝ) + (t : ℝ) * Complex.I))‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      fun i hi => norm_sum_block_cpow_le_one data hz2 hw (Finset.mem_of_mem_erase hi) t
  calc ‖∑ q ∈ data.block i₀, (q : ℂ) ^ (-((1 : ℝ) + (t : ℝ) * Complex.I))‖ *
        ∏ i ∈ data.indices.erase i₀,
          ‖∑ q ∈ data.block i, (q : ℂ) ^ (-((1 : ℝ) + (t : ℝ) * Complex.I))‖
      ≤ Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)) * 1 :=
        mul_le_mul h1 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_one _

end

end RHTower.Sieve
