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

end

end RHTower
