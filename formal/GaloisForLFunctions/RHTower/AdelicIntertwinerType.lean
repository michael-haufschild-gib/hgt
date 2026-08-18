import GaloisForLFunctions.PNTPlus.Consequences
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.RHTower.AdelicIntertwinerSaturation
import GaloisForLFunctions.RHTower.AcceleratedWoldType

/-!
# The restricted adelic Weyl comparison is already saturated

The finite tensor of unramified intertwiners over the primes below the cutoff has logarithm
`(2c + o(1)) ϑ(N)`: the local logarithms are `2c log p` up to a `p^{−(1−2c)}` defect whose sum over
the primes is `o(N)` because `2c < 1`, and the prime number theorem turns the leading term into
`2c N`.  Every positive multiple of `ϑ` has the maximal accelerated Wold type `e^{−γ}`, so the
standard adelic comparison saturates the accelerated invariant whatever the drift.
-/

open Filter Asymptotics Topology

namespace RHTower

theorem finsum_prime_log_eq_sum_primesBelow (n : ℕ) :
    ∑ᶠ (p : ℕ) (_ : p ≤ n) (_ : Nat.Prime p), Real.log (p : ℝ)
      = ∑ p ∈ Nat.primesBelow (n + 1), Real.log (p : ℝ) := by
  rw [← finsum_mem_coe_finset]
  refine finsum_congr fun p => ?_
  by_cases hp : Nat.Prime p
  · by_cases hpn : p ≤ n
    · simp [hp, hpn, Nat.mem_primesBelow]
    · simp [hp, hpn, Nat.mem_primesBelow]
  · simp [hp, Nat.mem_primesBelow]

/-- **The prime number theorem in the form the prime tensor uses**: the logarithmic mass of the
primes below the cutoff is asymptotic to the cutoff. -/
theorem tendsto_sum_primesBelow_log_div :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) / (N : ℝ))
      atTop (nhds 1) := by
  have hne : ∀ᶠ n : ℕ in atTop, ((n : ℝ)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Nat.cast_ne_zero.mpr (by omega)
  have hbase : Tendsto (fun n : ℕ =>
      (∑ᶠ (p : ℕ) (_ : p ≤ n) (_ : Nat.Prime p), Real.log (p : ℝ)) / (n : ℝ))
      atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hne).mp chebyshev_asymptotic_finsum
  have hshift : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun a ha => by omega⟩
  have hcomp := hbase.comp hshift
  have hratio : Tendsto (fun N : ℕ => (((N - 1 : ℕ) : ℝ)) / (N : ℝ)) atTop (nhds 1) := by
    have h : ∀ᶠ N : ℕ in atTop, (((N - 1 : ℕ) : ℝ)) / (N : ℝ) = 1 - 1 / (N : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN1 : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hcast : (((N - 1 : ℕ) : ℝ)) = (N : ℝ) - 1 := by
        have : 1 ≤ N := hN
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      field_simp
    refine Tendsto.congr' (h.mono fun N hN => hN.symm) ?_
    have hz : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hz
  have hprod := hcomp.mul hratio
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNm : (N - 1) + 1 = N := by omega
  have hNr : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Function.comp_apply]
  rw [finsum_prime_log_eq_sum_primesBelow, hNm]
  rcases Nat.eq_zero_or_pos (N - 1) with h0 | h0
  · have hN1 : N = 1 := by omega
    subst hN1
    norm_num
  · have hne' : (((N - 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

theorem tendsto_sum_log_norm_intertwinerEigen_div {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (z : ℕ → ℂ) (hz : ∀ p : ℕ, ‖z p‖ ^ 2 = (p : ℝ) ^ (2 * c)) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ Nat.primesBelow N, Real.log ‖intertwinerEigen p (z p)‖) / (N : ℝ))
      atTop (nhds (2 * c)) := by
  classical
  set Cc : ℝ := 2 / (1 - (2 : ℝ) ^ (2 * c - 1)) with hCcdef
  have hμ1 : (2 : ℝ) ^ (2 * c - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hκ0 : (0 : ℝ) < 1 - (2 : ℝ) ^ (2 * c - 1) := by linarith
  have hCc0 : (0 : ℝ) < Cc := by rw [hCcdef]; positivity
  -- the defect sum
  set E : ℕ → ℝ := fun N =>
    ∑ p ∈ Nat.primesBelow N, (Real.log ‖intertwinerEigen p (z p)‖ - 2 * c * Real.log (p : ℝ))
    with hEdef
  have hEbound : ∀ N : ℕ, |E N| ≤ Cc * (1 + (N : ℝ) ^ (2 * c) / (2 * c)) := by
    intro N
    have hstep : |E N| ≤ ∑ p ∈ Nat.primesBelow N, Cc * (p : ℝ) ^ (2 * c - 1) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p hp => ?_)
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      exact abs_log_norm_intertwinerEigen_sub_le hc0 hc hp2 (hz p)
    refine le_trans hstep ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hCc0.le
    have hsub : Nat.primesBelow N ⊆ Finset.Icc 1 N := by
      intro p hp
      have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
      have hlt := Nat.lt_of_mem_primesBelow hp
      rw [Finset.mem_Icc]
      omega
    have hsum : ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (2 * c - 1)
        ≤ ∑ r ∈ Finset.Icc 1 N, (r : ℝ) ^ (-(1 - 2 * c)) := by
      have hcongr : ∀ p ∈ Nat.primesBelow N,
          (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (-(1 - 2 * c)) := by
        intro p _
        congr 1
        ring
      rw [Finset.sum_congr rfl hcongr]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => ?_
      positivity
    refine le_trans hsum ?_
    have hhead := sum_rpow_neg_head_le (c := 1 - 2 * c) (by linarith) (by linarith) N
    have hexp : (1 : ℝ) - (1 - 2 * c) = 2 * c := by ring
    rw [hexp] at hhead
    exact hhead
  have hzero : Tendsto (fun N : ℕ => E N / (N : ℝ)) atTop (nhds 0) := by
    have hup : Tendsto (fun N : ℕ => Cc * (1 + (N : ℝ) ^ (2 * c) / (2 * c)) / (N : ℝ))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * c - 1)) atTop (nhds 0) := by
        have hneg : Tendsto (fun x : ℝ => x ^ (2 * c - 1)) atTop (nhds 0) := by
          have := tendsto_rpow_neg_atTop (y := 1 - 2 * c) (by linarith)
          refine this.congr fun x => ?_
          congr 1
          ring
        exact hneg.comp tendsto_natCast_atTop_atTop
      have h3 : Tendsto (fun N : ℕ => Cc * ((1 : ℝ) / (N : ℝ)
          + (N : ℝ) ^ (2 * c - 1) / (2 * c))) atTop (nhds 0) := by
        have := (h1.add (h2.div_const (2 * c))).const_mul Cc
        simpa using this
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hpow : (N : ℝ) ^ (2 * c - 1) = (N : ℝ) ^ (2 * c) / (N : ℝ) := by
        have h : (N : ℝ) ^ (2 * c - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (2 * c) := by
          rw [← Real.rpow_add hNr]; congr 1; ring
        rw [Real.rpow_one] at h
        rw [eq_div_iff (ne_of_gt hNr)]
        exact h
      rw [hpow]
      field_simp
    refine squeeze_zero_norm' ?_ hup
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hNr]
    gcongr
    exact hEbound N
  have hmain : ∀ N : ℕ,
      (∑ p ∈ Nat.primesBelow N, Real.log ‖intertwinerEigen p (z p)‖) / (N : ℝ)
        = E N / (N : ℝ) + 2 * c * ((∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) / (N : ℝ)) := by
    intro N
    rw [hEdef]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  have hlim := hzero.add ((tendsto_sum_primesBelow_log_div).const_mul (2 * c))
  rw [zero_add, mul_one] at hlim
  exact hlim.congr fun N => (hmain N).symm


/-- **The finite intertwiner tensor saturates the accelerated type.**  Its logarithm grows
linearly in the cutoff with slope `2c`, and every positive slope gives the maximal boundary
type `e^{−γ}`. -/
theorem tendsto_mertensProduct_mul_ell2_intertwinerProduct {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (z : ℕ → ℂ) (hz : ∀ p : ℕ, ‖z p‖ ^ 2 = (p : ℝ) ^ (2 * c)) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
        ell2 (∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  classical
  have hfac : ∀ N : ℕ, ∀ p ∈ Nat.primesBelow N, 0 < ‖intertwinerEigen p (z p)‖ := by
    intro N p hp
    exact norm_intertwinerEigen_pos hc0 hc (Nat.prime_of_mem_primesBelow hp).two_le (hz p)
  have hSpos : ∀ N : ℕ, 0 < ∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖ :=
    fun N => Finset.prod_pos (hfac N)
  have hlogS : ∀ N : ℕ, Real.log (∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖)
      = ∑ p ∈ Nat.primesBelow N, Real.log ‖intertwinerEigen p (z p)‖ := by
    intro N
    exact Real.log_prod fun p hp => ne_of_gt (hfac N p hp)
  refine tendsto_mertensProduct_mul_ell2_of_log_linear (by linarith : (0:ℝ) < 2 * c)
    (Filter.Eventually.of_forall hSpos) ?_
  refine (tendsto_sum_log_norm_intertwinerEigen_div hc0 hc z hz).congr fun N => ?_
  rw [hlogS N]

/-- The square root of the tensor has half the slope, hence the same saturated type. -/
theorem tendsto_mertensProduct_mul_ell2_sqrt_intertwinerProduct {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 2) (z : ℕ → ℂ) (hz : ∀ p : ℕ, ‖z p‖ ^ 2 = (p : ℝ) ^ (2 * c)) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
        ell2 (Real.sqrt (∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖))) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  classical
  have hfac : ∀ N : ℕ, ∀ p ∈ Nat.primesBelow N, 0 < ‖intertwinerEigen p (z p)‖ := by
    intro N p hp
    exact norm_intertwinerEigen_pos hc0 hc (Nat.prime_of_mem_primesBelow hp).two_le (hz p)
  have hSpos : ∀ N : ℕ, 0 < ∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖ :=
    fun N => Finset.prod_pos (hfac N)
  have hlogS : ∀ N : ℕ, Real.log (∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖)
      = ∑ p ∈ Nat.primesBelow N, Real.log ‖intertwinerEigen p (z p)‖ := by
    intro N
    exact Real.log_prod fun p hp => ne_of_gt (hfac N p hp)
  refine tendsto_mertensProduct_mul_ell2_of_log_linear hc0
    (Filter.Eventually.of_forall fun N => Real.sqrt_pos.mpr (hSpos N)) ?_
  have hhalf := (tendsto_sum_log_norm_intertwinerEigen_div hc0 hc z hz).div_const 2
  have hval : (2 * c) / 2 = c := by ring
  rw [hval] at hhalf
  refine hhalf.congr fun N => ?_
  rw [Real.log_sqrt (hSpos N).le, hlogS N]
  ring

/-- **`(18k)`: the accelerated type of any scalar-normalized finite tensor containing the full
Iwahori record is at least `e^{−γ}`.**  Only the two-sided comparison
`‖T‖ ‖T⁻¹‖ ≥ ∏ |λ_p|` is used, and it is unchanged by a scalar gauge. -/
theorem eventually_lt_mertensProduct_mul_ell2_intertwiner {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (z : ℕ → ℂ) (hz : ∀ p : ℕ, ‖z p‖ ^ 2 = (p : ℝ) ^ (2 * c))
    (T : ℕ → ℝ) (hT0 : ∀ N, 0 ≤ T N)
    (hT : ∀ N, (∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖) ≤ T N ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-Real.eulerMascheroniConstant) - ε < mertensPrimeProductBelow N * ell2 (T N) := by
  classical
  have hfac : ∀ N : ℕ, ∀ p ∈ Nat.primesBelow N, 0 < ‖intertwinerEigen p (z p)‖ := by
    intro N p hp
    exact norm_intertwinerEigen_pos hc0 hc (Nat.prime_of_mem_primesBelow hp).two_le (hz p)
  have hSpos : ∀ N : ℕ, 0 < ∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖ :=
    fun N => Finset.prod_pos (hfac N)
  have hsqrtle : ∀ N : ℕ,
      Real.sqrt (∏ p ∈ Nat.primesBelow N, ‖intertwinerEigen p (z p)‖) ≤ T N := by
    intro N
    have h := Real.sqrt_le_sqrt (hT N)
    rwa [Real.sqrt_sq (hT0 N)] at h
  have hlim := tendsto_mertensProduct_mul_ell2_sqrt_intertwinerProduct hc0 hc z hz
  have hev := hlim.eventually (eventually_gt_nhds
    (show Real.exp (-Real.eulerMascheroniConstant) - ε
      < Real.exp (-Real.eulerMascheroniConstant) by linarith))
  filter_upwards [hev] with N hN
  refine lt_of_lt_of_le hN ?_
  refine mul_le_mul_of_nonneg_left ?_ (mertensPrimeProductBelow_pos N).le
  exact ell2_mono (Real.sqrt_nonneg _) (hsqrtle N)


/-- **`(21a)`: the oriented prime Lyapunov rate of the Weyl block, normalized by `ϑ`.** -/
theorem tendsto_sum_log_norm_intertwinerEigen_div_theta {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (z : ℕ → ℂ) (hz : ∀ p : ℕ, ‖z p‖ ^ 2 = (p : ℝ) ^ (2 * c)) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesBelow N, Real.log ‖intertwinerEigen p (z p)‖)
        / (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ))) atTop (nhds (2 * c)) := by
  classical
  have hnum := tendsto_sum_log_norm_intertwinerEigen_div hc0 hc z hz
  have hden := tendsto_sum_primesBelow_log_div
  have hdiv := hnum.div hden one_ne_zero
  rw [div_one] at hdiv
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) := by
    have hev := hden.eventually (eventually_gt_nhds (show (1 : ℝ) / 2 < 1 by norm_num))
    filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    by_contra hle
    rw [not_lt] at hle
    have : (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) / (N : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hle hNr.le
    linarith
  refine hdiv.congr' ?_
  filter_upwards [hpos, eventually_gt_atTop 0] with N hN hN0
  have hNr : ((N : ℝ)) ≠ 0 := by
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    exact ne_of_gt hN'
  have hBne : (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) ≠ 0 := ne_of_gt hN
  simp only [Pi.div_apply]
  field_simp

/-! ## One modular charge in four charts -/

/-- **`(21)`, `(21b)`, `(21c)`: the four coordinates of the modular charge determine one another.**
The Hellinger acceleration, the positive-shell reflection rate, the Xi Julia residue and the adelic
Weyl drift are the same number in four normalizations; the Weyl map pays exactly the modular
retuning cost `1 − β_ρ`. -/
theorem modularCharge_dictionary {reρ mρ rShell reRes aHel rWeyl βρ : ℝ} (hm : 0 < mρ)
    (hShell : rShell = (2 * reρ - 1) * Real.log 2)
    (hRes : reRes = mρ * (1 / 2 - reρ))
    (hHel : aHel = 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - reρ))
    (hWeyl : rWeyl = 2 * (1 / 2 - reρ))
    (hβ : βρ = 2 * reρ) :
    aHel = -(Real.exp (-Real.eulerMascheroniConstant) / Real.log 2) * rShell ∧
      aHel = 2 * Real.exp (-Real.eulerMascheroniConstant) / mρ * reRes ∧
      rWeyl = -(rShell / Real.log 2) ∧
      rWeyl = 2 / mρ * reRes ∧
      rWeyl = Real.exp Real.eulerMascheroniConstant * aHel ∧
      rWeyl = 1 - βρ := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hmne : mρ ≠ 0 := ne_of_gt hm
  have hexp : Real.exp Real.eulerMascheroniConstant
      * Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]
    simp
  subst hShell hRes hHel hWeyl hβ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
  · field_simp
    ring
  · field_simp
  · linear_combination (-2 * (1 / 2 - reρ)) * hexp
  · ring


end RHTower
