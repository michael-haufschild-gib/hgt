import GaloisForLFunctions.RHTower.XiMassBottomPrimeAtomization
import Mathlib.NumberTheory.LSeries.PrimesInAP

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem norm_stripFourier_xiMassAnalyticTest_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u w : ℝ) :
    ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)‖ ≤
      ∫ x : ℝ, Real.exp (-(σ * |x|)) := by
  unfold stripFourier
  apply norm_integral_le_of_norm_le
  · exact integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hσ
  · refine Filter.Eventually.of_forall fun x => ?_
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    have hg := norm_xiMassAnalyticTest_le (τ := ((σ : ℂ) + u * I))
      ha (by simpa using hσ.le) hmem
    rw [norm_mul, Complex.norm_exp]
    have hphase : (-(I * (w : ℂ) * (x : ℂ))).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one]
    simpa using hg

def xiMassPrimePowerCriticalWeight (p : Nat.Primes) (k : ℕ) : ℝ :=
  ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (1 / 2 : ℂ) ((p : ℕ) ^ (k + 1))‖

theorem xiMassPrimePowerCriticalWeight_eq (p : Nat.Primes) (k : ℕ) :
    xiMassPrimePowerCriticalWeight p k =
      Real.log (p : ℝ) * (p : ℝ) ^ (-((k + 1 : ℝ) / 2)) := by
  have hpPow : 0 < (p : ℕ) ^ (k + 1) := pow_pos p.prop.pos _
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  rw [xiMassPrimePowerCriticalWeight, LSeries.norm_term_eq, if_neg hpPow.ne']
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos
    hpR)]
  rw [Nat.cast_pow, div_eq_mul_inv, ← Real.rpow_neg (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  norm_num
  ring

theorem norm_xiMassCenteredPrimeAtom_primePower_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ)
    (p : Nat.Primes) (k : ℕ) :
    ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I) ((p : ℕ) ^ (k + 1))‖ ≤
      xiMassPrimePowerCriticalWeight p k *
        (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
  rw [xiMassCenteredPrimeAtom, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_stripFourier_xiMassAnalyticTest_vertical_le ha hσ u
      (Real.log ((((p : ℕ) ^ (k + 1) : ℕ)) : ℝ)))
    (norm_nonneg _)

theorem xiMassCenteredPrimeAtom_support_primePower {a : ℝ} {τ : ℂ} :
    Function.support (xiMassCenteredPrimeAtom a τ) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpow
  apply hn
  rw [xiMassCenteredPrimeAtom]
  have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_zero, zero_mul]
  · rw [LSeries.term_of_ne_zero hn0, hΛ]
    simp

theorem tsum_xiMassCenteredPrimeAtom_eq_primePower
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∑' n : ℕ, xiMassCenteredPrimeAtom a τ n) =
      ∑' (p : Nat.Primes) (k : ℕ),
        xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ (k + 1)) := by
  exact tsum_eq_tsum_primes_of_support_subset_prime_powers
    (summable_xiMassCenteredPrimeAtom hhalf hca hτ)
    xiMassCenteredPrimeAtom_support_primePower

theorem summable_primeLog_mul_inv_rpow_add
    (β : ℝ) (hβ : 1 < β) :
    Summable (fun pk : Nat.Primes × ℕ =>
      Real.log (pk.1 : ℝ) * ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + β)) := by
  have hp0 (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr p.prop.pos)
  have hp1 (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast p.prop.one_lt)
  have hbase : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * (p : ℝ) ^ (-β)) := by
    have hAbs : Summable (fun p : Nat.Primes =>
        |Real.log (p : ℝ)| * (p : ℝ) ^ (-β)) := by
      have h := (summable_abs_log_natCast_pow_mul_rpow_neg 1 β hβ).comp_injective
        (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
      simpa only [Function.comp_apply, pow_one] using! h
    apply hAbs.of_nonneg_of_le
    · intro p
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity)
    intro p
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  conv => enter [1, pk]; rw [Real.rpow_add (hp0 pk.1), Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun pk => mul_nonneg
    (Real.log_nonneg (by exact_mod_cast pk.1.prop.one_le)) (by positivity))).mpr ⟨?_, ?_⟩
  · intro p
    have hgeo := (summable_geometric_of_lt_one (hp0 p).le (hp1 p)).mul_left
      (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β)
    apply hgeo.congr
    intro k
    ring
  · have hcoeff : Summable (fun p : Nat.Primes =>
        Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β) := by
      apply hbase.congr
      intro p
      rw [Real.inv_rpow (Nat.cast_nonneg _),
        Real.rpow_neg (Nat.cast_nonneg _)]
    apply (hcoeff.mul_left 2).of_nonneg_of_le
      (fun p => tsum_nonneg fun k => mul_nonneg
        (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity))
    intro p
    rw [show (fun k : ℕ =>
        Real.log (p : ℝ) * (((p : ℝ)⁻¹) ^ k * ((p : ℝ)⁻¹) ^ β)) =
        fun k => (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β) * ((p : ℝ)⁻¹) ^ k by
      funext k
      ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (hp0 p).le (hp1 p)]
    have hden : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (hp1 p)
    have hinv : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hden zero_lt_two, le_sub_comm,
        show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num,
        inv_le_inv₀ (by exact_mod_cast p.prop.pos) zero_lt_two]
      exact_mod_cast p.prop.two_le
    have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
    have hcoeffNonneg :
        0 ≤ Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β :=
      mul_nonneg (Real.log_nonneg hpOne) (Real.rpow_nonneg (hp0 p).le _)
    calc
      (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β) *
          (1 - (p : ℝ)⁻¹)⁻¹ ≤
          (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β) * 2 :=
        mul_le_mul_of_nonneg_left hinv hcoeffNonneg
      _ = 2 * (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ β) := by ring

theorem summable_xiMassPrimePowerCriticalWeight_high :
    Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) := by
  have he : Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 2)) := by
    have h := summable_primeLog_mul_inv_rpow_add (3 / 2) (by norm_num)
    apply h.congr
    rintro ⟨p, k⟩
    rw [xiMassPrimePowerCriticalWeight_eq]
    congr 1
    rw [Real.inv_rpow (Nat.cast_nonneg _),
      Real.rpow_neg (Nat.cast_nonneg _)]
    congr 2
    push_cast
    ring
  have ho : Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 1 + 2)) := by
    have h := summable_primeLog_mul_inv_rpow_add 2 (by norm_num)
    apply h.congr
    rintro ⟨p, k⟩
    rw [xiMassPrimePowerCriticalWeight_eq]
    congr 1
    rw [Real.inv_rpow (Nat.cast_nonneg _),
      Real.rpow_neg (Nat.cast_nonneg _)]
    congr 2
    push_cast
    ring
  let e : (Nat.Primes × ℕ) ⊕ (Nat.Primes × ℕ) ≃ Nat.Primes × ℕ :=
    (Equiv.prodSumDistrib Nat.Primes ℕ ℕ).symm.trans
      (Equiv.prodCongr (Equiv.refl Nat.Primes) Equiv.natSumNatEquivNat)
  apply e.summable_iff.mp
  apply Summable.sum _
  · simpa [e, Function.comp_def, Equiv.trans_apply,
      Equiv.prodSumDistrib_symm_apply_left, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.natSumNatEquivNat_apply, Sum.elim_inl,
      Prod.fst, Prod.snd, Nat.reduceAdd, zero_add] using he
  · simpa [e, Function.comp_def, Equiv.trans_apply,
      Equiv.prodSumDistrib_symm_apply_right, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.natSumNatEquivNat_apply, Sum.elim_inr,
      Prod.fst, Prod.snd] using ho

def xiMassHighPrimePowerTail (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    xiMassCenteredPrimeAtom a τ ((pk.1 : ℕ) ^ (pk.2 + 3))

theorem summable_norm_xiMassHighPrimePowerAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
        ((pk.1 : ℕ) ^ (pk.2 + 3))‖) := by
  have hmajorant : Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) *
        (∫ x : ℝ, Real.exp (-(σ * |x|)))) :=
    summable_xiMassPrimePowerCriticalWeight_high.mul_right _
  apply hmajorant.of_nonneg_of_le (fun _ => norm_nonneg _)
  rintro ⟨p, k⟩
  simpa only [Prod.fst, Prod.snd, add_assoc] using
    norm_xiMassCenteredPrimeAtom_primePower_le ha hσ u p (k + 2)

theorem summable_xiMassHighPrimePowerAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
        ((pk.1 : ℕ) ^ (pk.2 + 3))) :=
  summable_norm_iff.mp (summable_norm_xiMassHighPrimePowerAtom ha hσ u)

theorem norm_xiMassHighPrimePowerTail_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)‖ ≤
      (∑' pk : Nat.Primes × ℕ,
        xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) *
          (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
  have hnorm := summable_norm_xiMassHighPrimePowerAtom ha hσ u
  have hmajorant : Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) *
        (∫ x : ℝ, Real.exp (-(σ * |x|)))) :=
    summable_xiMassPrimePowerCriticalWeight_high.mul_right _
  calc
    ‖xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)‖ ≤
        ∑' pk : Nat.Primes × ℕ,
          ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
            ((pk.1 : ℕ) ^ (pk.2 + 3))‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' pk : Nat.Primes × ℕ,
          xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) *
            (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
      apply hnorm.tsum_le_tsum
      · rintro ⟨p, k⟩
        simpa only [Prod.fst, Prod.snd, add_assoc] using
          norm_xiMassCenteredPrimeAtom_primePower_le ha hσ u p (k + 2)
      · exact hmajorant
    _ = _ := tsum_mul_right

theorem tsum_xiMassCenteredPrimeAtom_eq_prime_add_square_add_high
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∑' n : ℕ, xiMassCenteredPrimeAtom a τ n) =
      (∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ (p : ℕ)) +
      (∑' p : Nat.Primes,
        xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ 2)) +
      xiMassHighPrimePowerTail a τ := by
  let f : ℕ → ℂ := xiMassCenteredPrimeAtom a τ
  have hf : Summable f := summable_xiMassCenteredPrimeAtom hhalf hca hτ
  have hpow : Summable (fun pk : Nat.Primes × ℕ =>
      f ((pk.1 : ℕ) ^ (pk.2 + 1))) := by
    simpa only [f, eulerPrimePowerNat] using!
      hf.comp_injective eulerPrimePowerNat_injective
  have hprime : Summable (fun p : Nat.Primes => f (p : ℕ)) := by
    have h := hf.comp_injective
      (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
    simpa only [Function.comp_apply] using! h
  have hsquare : Summable (fun p : Nat.Primes => f ((p : ℕ) ^ 2)) := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) ^ 2) := by
      intro p q hpq
      exact Subtype.ext (Nat.pow_left_injective (by norm_num) hpq)
    have h := hf.comp_injective hinj
    simpa only [Function.comp_apply] using! h
  have ha : 0 < a := by linarith
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hhigh : Summable (fun pk : Nat.Primes × ℕ =>
      f ((pk.1 : ℕ) ^ (pk.2 + 3))) := by
    simpa only [f, hτform] using
      summable_xiMassHighPrimePowerAtom ha hτ τ.im
  have hhighOuter : Summable (fun p : Nat.Primes =>
      ∑' k : ℕ, f ((p : ℕ) ^ (k + 3))) := hhigh.prod
  have hinner (p : Nat.Primes) :
      (∑' k : ℕ, f ((p : ℕ) ^ (k + 1))) =
        f (p : ℕ) + f ((p : ℕ) ^ 2) +
          ∑' k : ℕ, f ((p : ℕ) ^ (k + 3)) := by
    have hp : Summable (fun k : ℕ => f ((p : ℕ) ^ (k + 1))) := by
      have h := hpow.comp_injective
        (i := fun k : ℕ => (p, k)) (fun _ _ h => congrArg Prod.snd h)
      simpa only [Function.comp_apply] using! h
    have hpShift : Summable (fun k : ℕ => f ((p : ℕ) ^ ((k + 1) + 1))) :=
      hp.comp_injective Nat.succ_injective
    calc
      (∑' k : ℕ, f ((p : ℕ) ^ (k + 1))) =
          f ((p : ℕ) ^ (0 + 1)) +
            ∑' k : ℕ, f ((p : ℕ) ^ ((k + 1) + 1)) :=
        hp.tsum_eq_zero_add
      _ = f ((p : ℕ) ^ (0 + 1)) +
          (f ((p : ℕ) ^ ((0 + 1) + 1)) +
            ∑' k : ℕ, f ((p : ℕ) ^ (((k + 1) + 1) + 1))) := by
        rw [hpShift.tsum_eq_zero_add]
      _ = f (p : ℕ) +
          (f ((p : ℕ) ^ 2) +
            ∑' k : ℕ, f ((p : ℕ) ^ (k + 3))) := by
        have htail :
            (∑' k : ℕ, f ((p : ℕ) ^ (((k + 1) + 1) + 1))) =
              ∑' k : ℕ, f ((p : ℕ) ^ (k + 3)) := by
          apply tsum_congr
          intro k
          congr 2
        rw [htail]
        norm_num
      _ = f (p : ℕ) + f ((p : ℕ) ^ 2) +
          ∑' k : ℕ, f ((p : ℕ) ^ (k + 3)) := by
        rw [add_assoc]
  calc
    (∑' n : ℕ, xiMassCenteredPrimeAtom a τ n) =
        ∑' p : Nat.Primes, ∑' k : ℕ,
          xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ (k + 1)) :=
      tsum_xiMassCenteredPrimeAtom_eq_primePower hhalf hca hτ
    _ = ∑' p : Nat.Primes,
        (f (p : ℕ) + f ((p : ℕ) ^ 2) +
          ∑' k : ℕ, f ((p : ℕ) ^ (k + 3))) := by
      exact tsum_congr hinner
    _ = (∑' p : Nat.Primes, f (p : ℕ)) +
        (∑' p : Nat.Primes, f ((p : ℕ) ^ 2)) +
          ∑' p : Nat.Primes, ∑' k : ℕ,
            f ((p : ℕ) ^ (k + 3)) := by
      rw [(hprime.add hsquare).tsum_add hhighOuter,
        hprime.tsum_add hsquare]
    _ = _ := by
      rw [← hhigh.tsum_prod]
      rfl

theorem integral_xiMassBottomPrimeIntegrand_eq_prime_add_square_add_high
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomPrimeIntegrand a c τ x) =
      (∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ (p : ℕ)) +
      (∑' p : Nat.Primes,
        xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ 2)) +
      xiMassHighPrimePowerTail a τ := by
  rw [integral_xiMassBottomPrimeIntegrand_eq_tsum_centeredAtom hhalf hca hτ,
    tsum_xiMassCenteredPrimeAtom_eq_prime_add_square_add_high hhalf hca hτ]

end

end RHTower
