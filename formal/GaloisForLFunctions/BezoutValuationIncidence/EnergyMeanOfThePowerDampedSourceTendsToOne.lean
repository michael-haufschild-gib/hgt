import GaloisForLFunctions.BezoutValuationIncidence.BaezDuarteEnergyOfThePowerDampedMobiusRows
import GaloisForLFunctions.BezoutValuationIncidence.NaturalCutoffMultiDepthCofactorAndConditionalTailBridge
import GaloisForLFunctions.RHTower.ZetaDerivResidue

/-!
# The energy mean of the power-damped source tends to one

The energy mean is the von Mangoldt readout of the cofactor row,
`m(ε, Q) = -Σ_{2 ≤ n ≤ Q+1} Y_ε(n) Λ(n)`. Only primes contribute: at a prime power `p^k`, `k ≥ 2`,
the weight vanishes because the modulus is not squarefree. At a prime,
`Y_ε(p) = -1/(ζ(1+ε)(p^{1+ε} - 1))`. Hence

`m(ε, Q) = (1/ζ(1+ε)) Σ_{p ≤ Q+1} log p/(p^{1+ε} - 1)`.

Regrouping the von Mangoldt series by prime gives `Σ_p log p/(p^s - 1) = -ζ'(s)/ζ(s)`, since
each prime contributes a geometric series of its powers. So, as `Q → ∞`,

`m(ε, Q) → m(ε) = -ζ'(1+ε)/ζ(1+ε)²`,

and the residues `(s-1)ζ(s) → 1`, `(s-1)²ζ'(s) → -1` give `m(ε) → 1` as `ε → 0+`.

On the dual side of the frontier, the readout half of the question is settled. For every `η > 0` and
all small `ε > 0`, eventually in `Q`, `(1 - m(ε, Q))² < η`. Whether the power-damped cofactor rows
drive the Báez-Duarte residual `(1-m)² + V` to zero is therefore exactly whether their energy
variance `V(ε, Q)` can be made small along such a path.
-/

open Finset Filter Topology RHTower ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The von Mangoldt series regrouped by prime -/

/-- `Σ_n Λ(n) n^{-s} = Re(-ζ'(s)/ζ(s))` for real `s > 1`. -/
theorem hasSum_vonMangoldt_rpow {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-s))
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hsum := (LSeriesSummable_vonMangoldt hsC).hasSum
  rw [show ∑' n, LSeries.term (fun n => (Λ n : ℂ)) (s : ℂ) n =
    LSeries (fun n => (Λ n : ℂ)) (s : ℂ) from rfl, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsC]
    at hsum
  have hre := Complex.reCLM.hasSum hsum
  refine hre.congr_fun fun n => ?_
  simp only [Complex.reCLM_apply, LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n),
      show ((n : ℂ) ^ (s : ℂ)) = (((n : ℝ) ^ s : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl,
      ← Complex.ofReal_div, Complex.ofReal_re, div_eq_mul_inv]

/-- The geometric series of a prime: `Σ_{k ≥ 0} log p · p^{-s(k+1)} = log p/(p^s - 1)`. -/
theorem hasSum_prime_power_vonMangoldt {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    HasSum (fun k : ℕ => vonMangoldt ((p : ℕ) ^ (k + 1)) * (((p : ℕ) ^ (k + 1) : ℕ) : ℝ) ^ (-s))
      (Real.log p / (((p : ℕ) : ℝ) ^ s - 1)) := by
  have hp := p.prop
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp.one_lt
  have hps : 1 < ((p : ℕ) : ℝ) ^ s := Real.one_lt_rpow hp1 hs
  set r := (((p : ℕ) : ℝ) ^ s)⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (by positivity)
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hps
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.log p * r)
  have hval : Real.log p * r * (1 - r)⁻¹ = Real.log p / (((p : ℕ) : ℝ) ^ s - 1) := by
    simp only [r]
    field_simp
  rw [hval] at hgeom
  refine hgeom.congr_fun fun k => ?_
  rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  have hpow : ((((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) ^ (-s) = r * r ^ k := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm,
      Real.rpow_mul_natCast (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _), pow_succ']
  rw [hpow]
  ring

/-- **The prime form of the logarithmic derivative.** `Σ_p log p/(p^s - 1) = Re(-ζ'(s)/ζ(s))`. -/
theorem hasSum_primes_log_div {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : Nat.Primes => Real.log p / (((p : ℕ) : ℝ) ^ s - 1))
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re := by
  set g : ℕ → ℝ := fun n => vonMangoldt n * (n : ℝ) ^ (-s)
  have hg := hasSum_vonMangoldt_rpow hs
  set i : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 1)
  have hinj : Function.Injective i := by
    rintro ⟨p, a⟩ ⟨q, b⟩ h
    simp only [i] at h
    obtain ⟨hpq, hab⟩ := Nat.Prime.pow_inj p.prop q.prop h
    exact Prod.ext (Subtype.ext hpq) (by omega)
  have hoff : ∀ n ∉ Set.range i, g n = 0 := by
    intro n hn
    simp only [g]
    by_cases hpow : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := hpow
      exact absurd ⟨(⟨p, hp.nat_prime⟩, k - 1), by simp only [i]; congr 1; omega⟩ hn
    · rw [vonMangoldt_eq_zero_iff.mpr hpow, zero_mul]
  have hsig := (hinj.hasSum_iff hoff).mpr hg
  exact hsig.prod_fiberwise fun p => hasSum_prime_power_vonMangoldt (by linarith) p

/-! ## §2. The energy mean -/

/-- The energy mean as a sum over primes. -/
theorem pmPowerDampedRamanujanEnergyMean_eq_primes {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanEnergyMean ε Q =
      ∑ n ∈ range (Q + 2), (if n.Prime then (pmPowerDampedDivisorDensity ε).re *
        (Real.log n / ((n : ℝ) ^ (1 + ε) - 1)) else 0) := by
  rw [pmPowerDampedRamanujanEnergyMean, Finset.sum_range_succ' _ (Q + 1),
    Finset.sum_range_succ' _ Q, if_neg Nat.not_prime_one, if_neg Nat.not_prime_zero, add_zero,
    add_zero, ← sum_neg_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [show q + 1 + 1 = q + 2 from rfl]
  by_cases hp : (q + 2).Prime
  · rw [if_pos hp]
    have h := pmRealRamanujanWeight_prime hε hp
    simp only [pmRealRamanujanWeight] at h
    rw [h, vonMangoldt_apply_prime hp]
    ring
  · rw [if_neg hp]
    by_cases hpow : IsPrimePow (q + 2)
    · have hns : ¬ Squarefree (q + 2) := by
        intro hsq
        obtain ⟨r, k, hr, hk, hrk⟩ := hpow
        rw [← hrk, Nat.squarefree_pow_iff hr.nat_prime.ne_one hk.ne'] at hsq
        rw [← hrk, hsq.2, pow_one] at hp
        exact hp hr.nat_prime
      rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hns]
      simp
    · rw [vonMangoldt_eq_zero_iff.mpr hpow]
      simp

/-- **The energy mean converges** to `Re(1/ζ(1+ε)) · Re(-ζ'(1+ε)/ζ(1+ε))` as `Q → ∞`. -/
theorem tendsto_pmPowerDampedRamanujanEnergyMean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun Q : ℕ => pmPowerDampedRamanujanEnergyMean ε Q) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re *
        (-deriv riemannZeta ((1 + ε : ℝ) : ℂ) / riemannZeta ((1 + ε : ℝ) : ℂ)).re)) := by
  set D := (pmPowerDampedDivisorDensity ε).re
  set h : ℕ → ℝ := fun n => if n.Prime then D * (Real.log n / ((n : ℝ) ^ (1 + ε) - 1)) else 0
  have hprimes := (hasSum_primes_log_div (s := 1 + ε) (by linarith)).mul_left D
  have hnat : HasSum h (D * (-deriv riemannZeta ((1 + ε : ℝ) : ℂ) /
      riemannZeta ((1 + ε : ℝ) : ℂ)).re) := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
    have hoff : ∀ n ∉ Set.range (fun p : Nat.Primes => (p : ℕ)), h n = 0 := by
      intro n hn
      simp only [h]
      rw [if_neg]
      intro hpn
      exact hn ⟨⟨n, hpn⟩, rfl⟩
    refine (hinj.hasSum_iff hoff).mp ?_
    refine hprimes.congr_fun fun p => ?_
    simp only [Function.comp_apply, h, if_pos p.prop]
  have hlim := hnat.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  refine hlim.congr fun Q => ?_
  simp only [Function.comp_apply]
  rw [pmPowerDampedRamanujanEnergyMean_eq_primes hε Q]

/-! ## §3. The limit as `ε → 0` -/

/-- `-ζ'(s)/ζ(s)² → 1` as `s → 1`. -/
theorem tendsto_neg_deriv_div_sq_riemannZeta :
    Tendsto (fun s : ℂ => -deriv riemannZeta s / riemannZeta s ^ 2) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (𝓝 1) := by
  have h1 := riemannZeta_residue_one
  have h2 := tendsto_sub_one_sq_mul_deriv_riemannZeta
  have hq := (h2.neg).div (h1.pow 2) (by norm_num)
  simp only [neg_neg, one_pow, div_one] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (s - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs)
  simp only [Pi.div_apply]
  rw [mul_pow, neg_mul_eq_mul_neg, mul_div_mul_left _ _ hs1, neg_div]

/-- **The limit energy mean tends to one.** -/
theorem tendsto_limit_energyMean_one :
    Tendsto (fun ε : ℝ => (pmPowerDampedDivisorDensity ε).re *
        (-deriv riemannZeta ((1 + ε : ℝ) : ℂ) / riemannZeta ((1 + ε : ℝ) : ℂ)).re)
      (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝[>] 0) (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝 0) (𝓝 ((1 + 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact (ne_of_gt (Set.mem_Ioi.mp hε)) this
  have hc := (Complex.continuous_re.tendsto 1).comp (tendsto_neg_deriv_div_sq_riemannZeta.comp hmap)
  simp only [Complex.one_re] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  simp only [Function.comp_apply]
  set z : ℂ := ((1 + ε : ℝ) : ℂ) with hzdef
  have hzε : z = 1 + (ε : ℂ) := by rw [hzdef]; push_cast; ring
  -- both factors are real
  have hDz : pmPowerDampedDivisorDensity ε = 1 / riemannZeta z := by
    rw [pmPowerDampedDivisorDensity, hzε]
  have hDim : (1 / riemannZeta z).im = 0 := by
    rw [← hDz, pmPowerDampedDivisorDensity_eq_ofReal_re hε0, Complex.ofReal_im]
  have hLim : (-deriv riemannZeta z / riemannZeta z).im = 0 := by
    have h := hasSum_vonMangoldt_rpow (s := 1 + ε) (by linarith)
    have hsC : 1 < z.re := by rw [hzdef, Complex.ofReal_re]; linarith
    have hc := (LSeriesSummable_vonMangoldt hsC).hasSum
    rw [show ∑' n, LSeries.term (fun n => (Λ n : ℂ)) z n =
      LSeries (fun n => (Λ n : ℂ)) z from rfl, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsC]
      at hc
    have hreal := Complex.ofRealCLM.hasSum h
    have heq := hc.unique (hreal.congr_fun fun n => ?_)
    · rw [heq]
      simp
    · simp only [Complex.ofRealCLM_apply, LSeries.term_def]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n), hzdef,
          show ((n : ℂ) ^ ((1 + ε : ℝ) : ℂ)) = (((n : ℝ) ^ (1 + ε) : ℝ) : ℂ) by
            rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl]
        push_cast
        ring
  rw [show -deriv riemannZeta z / riemannZeta z ^ 2 =
      (1 / riemannZeta z) * (-deriv riemannZeta z / riemannZeta z) by ring,
    Complex.mul_re, hDim, zero_mul, sub_zero, hDz]

/-- **The readout half of the dual question is settled.** For every `η > 0` there is `δ > 0` such
that for every `ε ∈ (0, δ)`, eventually in `Q`, `(1 - m(ε, Q))² < η`. -/
theorem readout_defect_eventually_small {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ᶠ Q : ℕ in atTop,
      (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 < η := by
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  -- the limit mean is within `√η/2` of one for small `ε`
  have hlim := tendsto_limit_energyMean_one
  rw [Metric.tendsto_nhdsWithin_nhds] at hlim
  obtain ⟨δ, hδ, hclose⟩ := hlim (Real.sqrt η / 2) (by positivity)
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have hdist : dist ((pmPowerDampedDivisorDensity ε).re *
      (-deriv riemannZeta ((1 + ε : ℝ) : ℂ) / riemannZeta ((1 + ε : ℝ) : ℂ)).re) 1 <
      Real.sqrt η / 2 :=
    hclose hε (by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ)
  have hQ := (tendsto_pmPowerDampedRamanujanEnergyMean hε)
  rw [Metric.tendsto_atTop] at hQ
  obtain ⟨Q₀, hQ₀⟩ := hQ (Real.sqrt η / 2) (by positivity)
  filter_upwards [eventually_ge_atTop Q₀] with Q hQ
  have h1 := hQ₀ Q hQ
  rw [Real.dist_eq] at h1 hdist
  have habs : |1 - pmPowerDampedRamanujanEnergyMean ε Q| < Real.sqrt η := by
    have := abs_sub_lt_iff.mp h1
    have := abs_sub_lt_iff.mp hdist
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  calc (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2
      = |1 - pmPowerDampedRamanujanEnergyMean ε Q| ^ 2 := (sq_abs _).symm
    _ < Real.sqrt η ^ 2 := pow_lt_pow_left₀ habs (abs_nonneg _) two_ne_zero
    _ = η := Real.sq_sqrt hη.le

end

end GaloisForLFunctions.BezoutValuationIncidence
