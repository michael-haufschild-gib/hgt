import GaloisForLFunctions.RHTower.RouteEEulerDeficitIdentity
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount

/-!
# The saddle-aligned antiscale barrier

The logarithmic Euler deficit at the source-selected antiscale frequency is the transverse energy
up to a Mertens remainder:

```text
log(G_{σ,Y}/|M_{σ,Y}(t)|²) = ∑_{p ≤ Y} p^{-σ}|1 + p^{it}|² + O(log log Y)
                           = (π²/a³)(Y^a/(log Y)³)(1 + o(1)),        a = 1 - σ ≤ 1/2,
```

because `-log(1 - z) - z = O(z²)` once `z ≤ 1/2`, the local coordinates satisfy `z_p ≤ 4p^{-σ}`
and `p^{-2σ} ≤ 1/p`, and only the finitely many primes below `64` need the crude bound
`-log(1 - z_p) ≤ -log((1 - p^{-σ})²/(1 + p^{-σ})²)`.

Aligning the Euler saddle with the physical scale `X`, that is `Λ_{σ,Y} = 2 log X (1 + o(1))`,
turns the deficit into the subpower barrier

```text
|M_{σ,Y}(t)|²/G_{σ,Y} = X^{-π²/(a²(log Y)³) + o((log Y)^{-3})},
```

so for every fixed `c > 0` the saddle-aligned coercivity `|M|² ≤ G X^{-c}` is false for all large
`X`: the antiscale resonance is an explicit near-null vector of the unconditioned Euler norm.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## The logarithmic expansion -/

theorem neg_log_one_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    -Real.log (1 - z) ≤ z + 2 * z ^ 2 := by
  have hw : (0 : ℝ) < 1 - z := by linarith
  have hquad : (1 : ℝ) ≤ (1 + z + 2 * z ^ 2) * (1 - z) := by nlinarith
  have hinv : 1 / (1 - z) ≤ 1 + z + 2 * z ^ 2 := by
    rw [div_le_iff₀ hw]
    nlinarith [hquad]
  have hexp : (1 : ℝ) + z + 2 * z ^ 2 ≤ Real.exp (z + 2 * z ^ 2) := by
    have := Real.add_one_le_exp (z + 2 * z ^ 2)
    linarith
  have hle : 1 / (1 - z) ≤ Real.exp (z + 2 * z ^ 2) := le_trans hinv hexp
  have hlog : Real.log (1 / (1 - z)) ≤ z + 2 * z ^ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact hle
  rwa [Real.log_div one_ne_zero (ne_of_gt hw), Real.log_one, zero_sub] at hlog

theorem le_neg_log_one_sub {z : ℝ} (hz : z < 1) : z ≤ -Real.log (1 - z) := by
  have hw : (0 : ℝ) < 1 - z := by linarith
  have h := Real.log_le_sub_one_of_pos hw
  linarith

/-! ## The Mertens remainder of the deficit -/

/-- The finitely many small primes are absorbed into a constant. -/
def smallPrimeDeficitConst (a : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE 63,
    (-Real.log ((1 - (p : ℝ) ^ (a - 1)) ^ 2 / (1 + (p : ℝ) ^ (a - 1)) ^ 2)
      + 4 * (p : ℝ) ^ (a - 1))

/-- Each large prime contributes a quadratic remainder. -/
theorem abs_deficit_term_sub_energy_le {a t : ℝ} {p : ℕ} (hp : p.Prime) (ha2 : a ≤ 1 / 2)
    (hp64 : 64 ≤ p) :
    |(-Real.log (1 - eulerDeficitCoord a t p))
        - (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p))| ≤ 44 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hp64R : (64 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp64
  have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
  -- `u² ≤ 1/p`
  have husq : (p : ℝ) ^ (a - 1) * (p : ℝ) ^ (a - 1) ≤ 1 / (p : ℝ) := by
    have hadd : (p : ℝ) ^ (a - 1) * (p : ℝ) ^ (a - 1) = (p : ℝ) ^ (2 * a - 2) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hmono : (p : ℝ) ^ (2 * a - 2) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hneg : (p : ℝ) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_one, one_div]
    rw [hneg] at hmono
    rw [hadd]
    exact hmono
  have husmall : (p : ℝ) ^ (a - 1) ≤ 1 / 8 := by
    have h64 : (1 : ℝ) / (p : ℝ) ≤ 1 / 64 := by
      rw [div_le_div_iff₀ hp0 (by norm_num)]
      linarith
    nlinarith [hu, husq, h64]
  set u : ℝ := (p : ℝ) ^ (a - 1) with hu'
  set c : ℝ := 2 + 2 * Real.cos (t * Real.log p) with hc
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    have := Real.neg_one_le_cos (t * Real.log p)
    linarith
  have hc4 : c ≤ 4 := by
    rw [hc]
    have := Real.cos_le_one (t * Real.log p)
    linarith
  have hz : eulerDeficitCoord a t p = u * c / (1 + u) ^ 2 := rfl
  have hz0 : 0 ≤ eulerDeficitCoord a t p := eulerDeficitCoord_nonneg (a := a) (t := t) hp
  have hzle : eulerDeficitCoord a t p ≤ 4 * u := eulerDeficitCoord_le (a := a) (t := t) hp
  have hzhalf : eulerDeficitCoord a t p ≤ 1 / 2 := by
    have : 4 * u ≤ 4 * (1 / 8) := by linarith
    linarith
  -- the logarithmic part
  have hlog1 : eulerDeficitCoord a t p ≤ -Real.log (1 - eulerDeficitCoord a t p) :=
    le_neg_log_one_sub (by linarith)
  have hlog2 : -Real.log (1 - eulerDeficitCoord a t p)
      ≤ eulerDeficitCoord a t p + 2 * eulerDeficitCoord a t p ^ 2 :=
    neg_log_one_sub_le hz0 hzhalf
  have hsqle : eulerDeficitCoord a t p ^ 2 ≤ 16 * (u * u) := by
    nlinarith [hz0, hzle, hu]
  -- the denominator part
  have hdenpos : (0 : ℝ) < (1 + u) ^ 2 := by positivity
  have hdiffz : |eulerDeficitCoord a t p - u * c| ≤ 12 * (u * u) := by
    have hval : eulerDeficitCoord a t p - u * c = -(u * c * ((2 * u + u ^ 2) / (1 + u) ^ 2)) := by
      rw [hz]
      field_simp
      ring
    have hfrac : (0 : ℝ) ≤ (2 * u + u ^ 2) / (1 + u) ^ 2 := by positivity
    have hfracle : (2 * u + u ^ 2) / (1 + u) ^ 2 ≤ 3 * u := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hu, husmall]
    have huc : (0 : ℝ) ≤ u * c := by positivity
    have huc4 : u * c ≤ 4 * u := by nlinarith [hu, hc4]
    rw [hval, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith [huc, huc4, hfrac, hfracle, hu]
  have habs : |(-Real.log (1 - eulerDeficitCoord a t p)) - u * c| ≤ 44 * (u * u) := by
    have h1 : (-Real.log (1 - eulerDeficitCoord a t p)) - u * c
        ≤ 2 * eulerDeficitCoord a t p ^ 2 + |eulerDeficitCoord a t p - u * c| := by
      have := le_abs_self (eulerDeficitCoord a t p - u * c)
      linarith
    have h2 : -(2 * eulerDeficitCoord a t p ^ 2 + |eulerDeficitCoord a t p - u * c|)
        ≤ (-Real.log (1 - eulerDeficitCoord a t p)) - u * c := by
      have := neg_abs_le (eulerDeficitCoord a t p - u * c)
      linarith
    have h3 : 2 * eulerDeficitCoord a t p ^ 2 + |eulerDeficitCoord a t p - u * c|
        ≤ 44 * (u * u) := by linarith [hsqle, hdiffz]
    rw [abs_le]
    constructor <;> linarith
  calc |(-Real.log (1 - eulerDeficitCoord a t p)) - u * c| ≤ 44 * (u * u) := habs
    _ ≤ 44 * (1 / (p : ℝ)) := by linarith [husq]
    _ = 44 / (p : ℝ) := by ring

/-- Each small prime contributes a bounded amount. -/
theorem abs_deficit_term_sub_energy_le_const {a t : ℝ} {p : ℕ} (hp : p.Prime) (ha1 : a < 1) :
    |(-Real.log (1 - eulerDeficitCoord a t p))
        - (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p))|
      ≤ -Real.log ((1 - (p : ℝ) ^ (a - 1)) ^ 2 / (1 + (p : ℝ) ^ (a - 1)) ^ 2)
        + 4 * (p : ℝ) ^ (a - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
  have hult : (p : ℝ) ^ (a - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hzpos : 0 < 1 - eulerDeficitCoord a t p := one_sub_eulerDeficitCoord_pos hp ha1
  have hz0 : 0 ≤ eulerDeficitCoord a t p := eulerDeficitCoord_nonneg (a := a) (t := t) hp
  have hge := one_sub_eulerDeficitCoord_ge (a := a) (t := t) hp
  have hratio0 : (0 : ℝ) < (1 - (p : ℝ) ^ (a - 1)) ^ 2 / (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by
    have h1 : (0 : ℝ) < (1 - (p : ℝ) ^ (a - 1)) ^ 2 := by
      have : (0 : ℝ) < 1 - (p : ℝ) ^ (a - 1) := by linarith
      positivity
    have h2 : (0 : ℝ) < (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by positivity
    exact div_pos h1 h2
  have hlogmono : Real.log ((1 - (p : ℝ) ^ (a - 1)) ^ 2 / (1 + (p : ℝ) ^ (a - 1)) ^ 2)
      ≤ Real.log (1 - eulerDeficitCoord a t p) := Real.log_le_log hratio0 hge
  have hlogneg : Real.log (1 - eulerDeficitCoord a t p) ≤ 0 := by
    apply Real.log_nonpos (by linarith) (by linarith)
  have hc0 : (0 : ℝ) ≤ 2 + 2 * Real.cos (t * Real.log p) := by
    have := Real.neg_one_le_cos (t * Real.log p)
    linarith
  have hc4 : 2 + 2 * Real.cos (t * Real.log p) ≤ 4 := by
    have := Real.cos_le_one (t * Real.log p)
    linarith
  have hterm0 : (0 : ℝ) ≤ (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p)) :=
    mul_nonneg hu.le hc0
  have hterm4 : (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p)) ≤ 4 * (p : ℝ) ^ (a - 1) :=
    by nlinarith [hu, hc4]
  rw [abs_le]
  constructor <;> linarith

/-! ## The global deficit estimate -/

theorem primesLE_subset {m n : ℕ} (h : m ≤ n) : Nat.primesLE m ⊆ Nat.primesLE n := by
  intro p hp
  rw [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- **The deficit is the antiscale energy up to a Mertens remainder.** -/
theorem abs_eulerLogDeficit_sub_antiscaleEnergy_le {a t Y : ℝ} (ha2 : a ≤ 1 / 2) (hY : 63 ≤ Y) :
    |eulerLogDeficit a t Y - antiscaleEnergy a t Y|
      ≤ smallPrimeDeficitConst a + 44 * Sieve.mertensS ⌊Y⌋₊ := by
  have ha1 : a < 1 := by linarith
  have hfloor : 63 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hsub : Nat.primesLE 63 ⊆ Nat.primesLE ⌊Y⌋₊ := primesLE_subset hfloor
  set f : ℕ → ℝ := fun p =>
    (-Real.log (1 - eulerDeficitCoord a t p))
      - (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p)) with hf
  have hdiff : eulerLogDeficit a t Y - antiscaleEnergy a t Y
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊, f p := by
    rw [eulerLogDeficit, antiscaleEnergy, ← Finset.sum_sub_distrib]
  have hsplit : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, f p
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE 63, f p + ∑ p ∈ Nat.primesLE 63, f p :=
    (Finset.sum_sdiff hsub).symm
  have hlarge : ∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE 63, |f p|
      ≤ 44 * Sieve.mertensS ⌊Y⌋₊ := by
    have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE 63, |f p| ≤ 44 * (1 / (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      have hprime := Nat.prime_of_mem_primesLE hp.1
      have hp64 : 64 ≤ p := by
        by_contra hcon
        exact hp.2 (by
          rw [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hprime⟩)
      have h := abs_deficit_term_sub_energy_le (a := a) (t := t) hprime ha2 hp64
      calc |f p| ≤ 44 / (p : ℝ) := h
        _ = 44 * (1 / (p : ℝ)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Sieve.mertensS, Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) ?_
    intro p hp _
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    positivity
  have hsmall : ∑ p ∈ Nat.primesLE 63, |f p| ≤ smallPrimeDeficitConst a := by
    rw [smallPrimeDeficitConst]
    refine Finset.sum_le_sum fun p hp => ?_
    exact abs_deficit_term_sub_energy_le_const (a := a) (t := t)
      (Nat.prime_of_mem_primesLE hp) ha1
  calc |eulerLogDeficit a t Y - antiscaleEnergy a t Y|
      = |∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE 63, f p + ∑ p ∈ Nat.primesLE 63, f p| := by
        rw [hdiff, hsplit]
    _ ≤ |∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE 63, f p| + |∑ p ∈ Nat.primesLE 63, f p| :=
        abs_add_le _ _
    _ ≤ (∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE 63, |f p|) + ∑ p ∈ Nat.primesLE 63, |f p| := by
        exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 44 * Sieve.mertensS ⌊Y⌋₊ + smallPrimeDeficitConst a := add_le_add hlarge hsmall
    _ = smallPrimeDeficitConst a + 44 * Sieve.mertensS ⌊Y⌋₊ := by ring

/-! ## The transported barrier -/

/-- **The saddle-aligned antiscale barrier.**  At the source-selected antiscale frequency the
logarithmic Euler deficit is `(π²/a³) Y^a/(log Y)³ (1 + o(1))`. -/
theorem tendsto_eulerLogDeficit {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Tendsto (fun Y : ℝ => eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y ^ 3 / Y ^ a)
      atTop (nhds (Real.pi ^ 2 / a ^ 3)) := by
  have hE := tendsto_antiscaleEnergy ha0
  have hrem : Tendsto (fun Y : ℝ =>
      (eulerLogDeficit a (antiscaleFrequency a Y) Y - antiscaleEnergy a (antiscaleFrequency a Y) Y)
        * Real.log Y ^ 3 / Y ^ a) atTop (nhds 0) := by
    have hmaj : Tendsto (fun Y : ℝ =>
        (smallPrimeDeficitConst a + 44 * Sieve.mertensUpperConst) * (Real.log Y ^ 3 / Y ^ a)
          + 44 * (Real.log Y ^ 4 / Y ^ a)) atTop (nhds 0) := by
      have h1 := (HTGeometry.tendsto_logPow_div_rpow ha0 3).const_mul
        (smallPrimeDeficitConst a + 44 * Sieve.mertensUpperConst)
      have h2 := (HTGeometry.tendsto_logPow_div_rpow ha0 4).const_mul (44 : ℝ)
      rw [mul_zero] at h1 h2
      have h := h1.add h2
      rwa [add_zero] at h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (63 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    have hlog0 : (0 : ℝ) < Real.log Y := Real.log_pos (by linarith)
    have hlog1 : (1 : ℝ) ≤ Real.log Y := by
      have h3 : Real.log 3 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
      have : (1 : ℝ) < Real.log 3 := by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have hlt : Real.exp 1 < 3 := by linarith
        have hlog := Real.log_lt_log (Real.exp_pos 1) hlt
        rwa [Real.log_exp] at hlog
      linarith
    have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Y))
    have hfloorle : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0.le
    have hfloorpos : (0 : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := by
      have : (0 : ℕ) < ⌊Y⌋₊ := by omega
      exact_mod_cast this
    have hlogfloor : Real.log ⌊Y⌋₊ ≤ Real.log Y := Real.log_le_log hfloorpos hfloorle
    have hlogfloorpos : (0 : ℝ) < Real.log ⌊Y⌋₊ := by
      have h2 : (2 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor2
      have := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hloglog : Sieve.logLog ⌊Y⌋₊ ≤ Real.log Y := by
      rw [Sieve.logLog]
      calc Real.log (Real.log ⌊Y⌋₊) ≤ Real.log (Real.log Y) :=
            Real.log_le_log hlogfloorpos hlogfloor
        _ ≤ Real.log Y := by
            have := Real.log_le_sub_one_of_pos hlog0
            linarith
    have hmertens : Sieve.mertensS ⌊Y⌋₊ ≤ Real.log Y + Sieve.mertensUpperConst := by
      have h := Sieve.mertensS_le_logLog_add hfloor2
      linarith
    have hbound := abs_eulerLogDeficit_sub_antiscaleEnergy_le
      (a := a) (t := antiscaleFrequency a Y) ha2 hY
    have hnum : |eulerLogDeficit a (antiscaleFrequency a Y) Y
        - antiscaleEnergy a (antiscaleFrequency a Y) Y|
        ≤ smallPrimeDeficitConst a + 44 * Sieve.mertensUpperConst + 44 * Real.log Y := by
      linarith [hbound, hmertens]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hYa,
      abs_of_pos (by positivity : (0 : ℝ) < Real.log Y ^ 3)]
    have hstep : |eulerLogDeficit a (antiscaleFrequency a Y) Y
          - antiscaleEnergy a (antiscaleFrequency a Y) Y| * Real.log Y ^ 3 / Y ^ a
        ≤ (smallPrimeDeficitConst a + 44 * Sieve.mertensUpperConst + 44 * Real.log Y)
            * Real.log Y ^ 3 / Y ^ a := by
      apply div_le_div_of_nonneg_right _ hYa.le
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
    have hval : (smallPrimeDeficitConst a + 44 * Sieve.mertensUpperConst + 44 * Real.log Y)
          * Real.log Y ^ 3 / Y ^ a
        = (smallPrimeDeficitConst a + 44 * Sieve.mertensUpperConst) * (Real.log Y ^ 3 / Y ^ a)
          + 44 * (Real.log Y ^ 4 / Y ^ a) := by
      field_simp
    rw [← hval]
    exact hstep
  have hsum := hrem.add hE
  rw [zero_add] at hsum
  refine hsum.congr fun Y => ?_
  ring

/-- **Physical centering.**  When the Euler saddle is aligned with the physical scale `X`, the
antiscale deficit is `π²/(a²(log Y)³) log X (1 + o(1))`: the escape is subpower. -/
theorem tendsto_eulerLogDeficit_div_log {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    {Y X : ℕ → ℝ} (hY : Tendsto Y atTop atTop)
    (hcenter : Tendsto (fun n => saddleLogCenter (1 - a) (Y n) / (2 * Real.log (X n))) atTop
      (nhds 1)) :
    Tendsto (fun n => eulerLogDeficit a (antiscaleFrequency a (Y n)) (Y n)
        * Real.log (Y n) ^ 3 / Real.log (X n)) atTop (nhds (Real.pi ^ 2 / a ^ 2)) := by
  have hane : a ≠ 0 := ne_of_gt ha0
  have hσ : (1 : ℝ) / 2 ≤ 1 - a := by linarith
  have hσ1 : (1 : ℝ) - a < 1 := by linarith
  have hexp : (1 : ℝ) - (1 - a) = a := by ring
  have hcen : Tendsto (fun n => saddleLogCenter (1 - a) (Y n) / Y n ^ a) atTop
      (nhds (2 / a)) := by
    have h := (tendsto_saddleLogCenter hσ hσ1).comp hY
    rw [hexp] at h
    exact h
  have hdef : Tendsto (fun n => eulerLogDeficit a (antiscaleFrequency a (Y n)) (Y n)
      * Real.log (Y n) ^ 3 / Y n ^ a) atTop (nhds (Real.pi ^ 2 / a ^ 3)) :=
    (tendsto_eulerLogDeficit ha0 ha2).comp hY
  -- the scale comparison
  have hinv : Tendsto (fun n => (2 * Real.log (X n)) / saddleLogCenter (1 - a) (Y n)) atTop
      (nhds 1) := by
    have h := hcenter.inv₀ (by norm_num)
    rw [inv_one] at h
    refine h.congr fun n => ?_
    rw [← one_div, one_div_div]
  have hratio : Tendsto (fun n => 2 * Real.log (X n) / Y n ^ a) atTop (nhds (2 / a)) := by
    have h := hcen.mul hinv
    rw [mul_one] at h
    refine h.congr' ?_
    have hpos : ∀ᶠ n in atTop, 0 < saddleLogCenter (1 - a) (Y n) := by
      have hfin : Tendsto (fun n => saddleLogCenter (1 - a) (Y n) / Y n ^ a) atTop (nhds (2 / a)) :=
        hcen
      have hposlim : (0 : ℝ) < 2 / a := by positivity
      have heven := hfin.eventually (eventually_gt_nhds (by linarith : (0 : ℝ) < 2 / a))
      have hYpos : ∀ᶠ n in atTop, (0 : ℝ) < Y n ^ a := by
        filter_upwards [hY.eventually_gt_atTop 0] with n hn
        exact Real.rpow_pos_of_pos hn a
      filter_upwards [heven, hYpos] with n hn hYn
      by_contra hcon
      push_neg at hcon
      have : saddleLogCenter (1 - a) (Y n) / Y n ^ a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon hYn.le
      linarith
    filter_upwards [hpos] with n hn
    field_simp
  have hYa : Tendsto (fun n => Y n ^ a / (2 * Real.log (X n))) atTop (nhds (a / 2)) := by
    have h := hratio.inv₀ (by positivity)
    have hval : (2 / a)⁻¹ = a / 2 := by
      rw [inv_div]
    rw [hval] at h
    refine h.congr fun n => ?_
    rw [← one_div, one_div_div]
  have hYaX : Tendsto (fun n => Y n ^ a / Real.log (X n)) atTop (nhds a) := by
    have h := hYa.const_mul (2 : ℝ)
    have hval : (2 : ℝ) * (a / 2) = a := by ring
    rw [hval] at h
    refine h.congr fun n => ?_
    by_cases hzero : Real.log (X n) = 0
    · rw [hzero]
      simp
    · field_simp
  have hprod := hdef.mul hYaX
  have hval : Real.pi ^ 2 / a ^ 3 * a = Real.pi ^ 2 / a ^ 2 := by
    field_simp
  rw [hval] at hprod
  refine hprod.congr' ?_
  have hYpos : ∀ᶠ n in atTop, (0 : ℝ) < Y n ^ a := by
    filter_upwards [hY.eventually_gt_atTop 0] with n hn
    exact Real.rpow_pos_of_pos hn a
  filter_upwards [hYpos] with n hn
  field_simp

/-- **The saddle-aligned coercivity is false.**  For every fixed exponent the physical Euler
comparison `|M|² ≤ G·X^{-c}` fails for all large parameters: the antiscale frequency exhibits an
explicit near-null vector. -/
theorem eventually_saddle_coercivity_fails {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    {Y X : ℕ → ℝ} (hY : Tendsto Y atTop atTop) (hX : Tendsto X atTop atTop)
    (hcenter : Tendsto (fun n => saddleLogCenter (1 - a) (Y n) / (2 * Real.log (X n))) atTop
      (nhds 1)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop,
      positiveEulerSquare a (Y n) * X n ^ (-c)
        < eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n) := by
  have ha1 : a < 1 := by linarith
  have hmain := tendsto_eulerLogDeficit_div_log ha0 ha2 hY hcenter
  have hlogY : Tendsto (fun n => Real.log (Y n) ^ 3) atTop atTop := by
    have h := Real.tendsto_log_atTop.comp hY
    have h3 := Filter.Tendsto.atTop_mul_atTop₀ (Filter.Tendsto.atTop_mul_atTop₀ h h) h
    refine h3.congr fun n => ?_
    simp only [Function.comp_apply]
    ring
  have hquot : Tendsto (fun n => eulerLogDeficit a (antiscaleFrequency a (Y n)) (Y n)
      / Real.log (X n)) atTop (nhds 0) := by
    have h := hmain.div_atTop hlogY
    refine h.congr' ?_
    filter_upwards [hlogY.eventually_gt_atTop 0] with n hn
    have hlogne : Real.log (Y n) ≠ 0 := by
      intro hzero
      rw [hzero] at hn
      simp at hn
    field_simp
  have hsmall := hquot.eventually (eventually_lt_nhds hc)
  filter_upwards [hsmall, hX.eventually_gt_atTop 1, hY.eventually_gt_atTop 1] with n hn hXn hYn
  have hlogX : (0 : ℝ) < Real.log (X n) := Real.log_pos hXn
  have hXpos : (0 : ℝ) < X n := by linarith
  have hdeficit : eulerLogDeficit a (antiscaleFrequency a (Y n)) (Y n) < c * Real.log (X n) := by
    rw [div_lt_iff₀ hlogX] at hn
    linarith
  -- turn the logarithmic inequality into the product inequality
  have hpos : ∀ p ∈ Nat.primesLE ⌊Y n⌋₊, (0 : ℝ) < 1 - eulerDeficitCoord a
      (antiscaleFrequency a (Y n)) p := fun p hp =>
    one_sub_eulerDeficitCoord_pos (Nat.prime_of_mem_primesLE hp) ha1
  have hG : (0 : ℝ) < positiveEulerSquare a (Y n) := by
    rw [positiveEulerSquare]
    refine Finset.prod_pos fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
    positivity
  have hM : (0 : ℝ) < eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n) := by
    have hprod : (0 : ℝ) < ∏ p ∈ Nat.primesLE ⌊Y n⌋₊,
        (1 - eulerDeficitCoord a (antiscaleFrequency a (Y n)) p) := Finset.prod_pos hpos
    have hdiv : (0 : ℝ) < eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n)
        / positiveEulerSquare a (Y n) := by
      rw [eulerMellinNormSq_div_positiveEulerSquare]
      exact hprod
    have hmul := mul_pos hdiv hG
    rwa [div_mul_cancel₀ _ (ne_of_gt hG)] at hmul
  have hlogdef := eulerLogDeficit_eq_log_sub (a := a) (t := antiscaleFrequency a (Y n))
    (Y := Y n) ha1
  have hlogineq : Real.log (positiveEulerSquare a (Y n))
      < Real.log (eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n)) + c * Real.log (X n) := by
    rw [hlogdef] at hdeficit
    linarith
  have hrhs : Real.log (eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n))
      + c * Real.log (X n)
      = Real.log (eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n) * X n ^ c) := by
    rw [Real.log_mul (ne_of_gt hM) (by positivity), Real.log_rpow hXpos]
  rw [hrhs] at hlogineq
  have hcomp : positiveEulerSquare a (Y n)
      < eulerMellinNormSq a (antiscaleFrequency a (Y n)) (Y n) * X n ^ c := by
    have hXc : (0 : ℝ) < X n ^ c := Real.rpow_pos_of_pos hXpos c
    have := (Real.log_lt_log_iff hG (by positivity)).mp hlogineq
    exact this
  have hXc : (0 : ℝ) < X n ^ c := Real.rpow_pos_of_pos hXpos c
  have hneg : X n ^ (-c) = (X n ^ c)⁻¹ := by
    rw [Real.rpow_neg hXpos.le]
  rw [hneg, mul_inv_lt_iff₀ hXc]
  linarith [hcomp]

/-! ## Critical half density -/

/-- **Critical half-density barrier.**  At `σ = 1/2` the deficit is `8π² Y^{1/2}/(log Y)³`. -/
theorem tendsto_eulerLogDeficit_half :
    Tendsto (fun Y : ℝ =>
      eulerLogDeficit (1 / 2) (antiscaleFrequency (1 / 2) Y) Y * Real.log Y ^ 3 /
        Y ^ ((1 : ℝ) / 2)) atTop (nhds (8 * Real.pi ^ 2)) := by
  have h := tendsto_eulerLogDeficit (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  have hval : Real.pi ^ 2 / ((1 : ℝ) / 2) ^ 3 = 8 * Real.pi ^ 2 := by
    norm_num
    ring
  rwa [hval] at h

/-- **Critical half-density escape exponent.**  Under physical centering the critical escape is
`X^{-4π²/(log Y)³ + o((log Y)^{-3})}`. -/
theorem tendsto_eulerLogDeficit_div_log_half {Y X : ℕ → ℝ} (hY : Tendsto Y atTop atTop)
    (hcenter : Tendsto (fun n => saddleLogCenter (1 / 2) (Y n) / (2 * Real.log (X n))) atTop
      (nhds 1)) :
    Tendsto (fun n => eulerLogDeficit (1 / 2) (antiscaleFrequency (1 / 2) (Y n)) (Y n)
        * Real.log (Y n) ^ 3 / Real.log (X n)) atTop (nhds (4 * Real.pi ^ 2)) := by
  have hcenter' : Tendsto
      (fun n => saddleLogCenter (1 - (1 : ℝ) / 2) (Y n) / (2 * Real.log (X n))) atTop (nhds 1) := by
    have hval : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hval]
    exact hcenter
  have h := tendsto_eulerLogDeficit_div_log (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    hY hcenter'
  have hval : Real.pi ^ 2 / ((1 : ℝ) / 2) ^ 2 = 4 * Real.pi ^ 2 := by
    norm_num
    ring
  rwa [hval] at h

end

end RHTower
