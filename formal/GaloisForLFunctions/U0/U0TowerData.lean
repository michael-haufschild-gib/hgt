/-
# The tower radicand: iterate transport and well-definedness

The U0-side assembly layer on top of the landed section tower (`SectionTower*`,
`BottcherTowerData`): the depth-`k` radicand `F(z) = (T⁻¹(f^[j] z))^{2^{k−j}}` is well defined
on the extended domain because the tower functional equation transports iterates along the
annulus — `f^[m](T v) = T(v^{2^m})` whenever the endpoint modulus stays in range (the
intermediate moduli are monotone, so they never leave).  These are the exact bricks the
`towerdata` certificate of `U0TowerBridge.u0_phi_independence_of_towerData` consumes.
-/
import GaloisForLFunctions.Bottcher.BottcherTowerData
import GaloisForLFunctions.U0.U0TowerBridge

open Complex Set Bottcher

namespace U0TowerData

/-- **Iterate transport along the tower.**  `f^[m](T v) = T(v^{2^m})` as soon as both endpoint
moduli lie in the annulus: the intermediate moduli `‖v‖^{2^i}` are monotone in `i`, so every
intermediate stays inside and the functional equation chains. -/
theorem tower_iterate_eq {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀) (hrlo : 1 < rlo)
    {v : ℂ} (m : ℕ) (hv : v ∈ annulusSet rlo R₀)
    (hvm : v ^ (2 ^ m) ∈ annulusSet rlo R₀) :
    (quadratic c)^[m] (S.T v) = S.T (v ^ (2 ^ m)) := by
  induction m with
  | zero =>
    simp
  | succ m ihm =>
    have hnorm_v : rlo < ‖v‖ := hv.1
    have hv1 : 1 < ‖v‖ := lt_trans hrlo hnorm_v
    have hmid : v ^ (2 ^ m) ∈ annulusSet rlo R₀ := by
      constructor
      · calc rlo < ‖v‖ := hnorm_v
          _ ≤ ‖v‖ ^ (2 ^ m) := le_self_pow₀ (le_of_lt hv1) (by positivity)
          _ = ‖v ^ (2 ^ m)‖ := (norm_pow v (2 ^ m)).symm
      · have h1 : ‖v ^ (2 ^ m)‖ ^ (2 : ℕ) = ‖v ^ (2 ^ (m + 1))‖ := by
          rw [← norm_pow, ← pow_mul, ← pow_succ]
        have h2 : ‖v ^ (2 ^ (m + 1))‖ < R₀ := hvm.2
        nlinarith [norm_nonneg (v ^ (2 ^ m)), hvm.1,
          lt_trans (lt_trans zero_lt_one hrlo) hvm.1]
    have hsq : (v ^ (2 ^ m)) ^ (2 : ℕ) = v ^ (2 ^ (m + 1)) := by
      rw [← pow_mul, ← pow_succ]
    have hstep := S.fe (v ^ (2 ^ m)) hmid (by rw [hsq]; exact hvm)
    rw [Function.iterate_succ_apply', ihm hmid]
    rw [hsq] at hstep
    simp only [quadratic]
    exact hstep.symm

/-- **Radicand well-definedness.**  Two tower hits of the same orbit agree after the matching
dyadic powers: if `f^[j] z = T v` and `f^[j'] z = T v'` with `j ≤ j' ≤ k`, then
`v'^{2^{k−j'}} = v^{2^{k−j}}`. -/
theorem radicand_welldef {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀) (hrlo : 1 < rlo)
    {z : ℂ} {j j' k : ℕ} (hjj' : j ≤ j') (hj'k : j' ≤ k)
    {v v' : ℂ} (hv : v ∈ annulusSet rlo R₀) (hv' : v' ∈ annulusSet rlo R₀)
    (hj : (quadratic c)^[j] z = S.T v) (hj' : (quadratic c)^[j'] z = S.T v') :
    v' ^ (2 ^ (k - j')) = v ^ (2 ^ (k - j)) := by
  have horbit : (quadratic c)^[j' - j] (S.T v) = S.T v' := by
    rw [← hj, ← Function.iterate_add_apply]
    have : j' - j + j = j' := by omega
    rw [this, hj']
  -- moduli: ‖v‖^{2^{j'−j}} = ‖v'‖ via the Green level
  have hlev : greenFunctionDyn c (S.T v') = Real.log ‖v'‖ := S.level v' hv'
  have hlevv : greenFunctionDyn c (S.T v) = Real.log ‖v‖ := S.level v hv
  have hpow_mem : v ^ (2 ^ (j' - j)) ∈ annulusSet rlo R₀ := by
    constructor
    · have hv1 : 1 < ‖v‖ := lt_trans hrlo hv.1
      calc rlo < ‖v‖ := hv.1
        _ ≤ ‖v‖ ^ (2 ^ (j' - j)) := le_self_pow₀ (le_of_lt hv1) (by positivity)
        _ = ‖v ^ (2 ^ (j' - j))‖ := (norm_pow _ _).symm
    · -- the modulus matches ‖v'‖ < R₀ via the Green doubling
      have hdouble : greenFunctionDyn c ((quadratic c)^[j' - j] (S.T v))
          = 2 ^ (j' - j) * greenFunctionDyn c (S.T v) :=
        greenFunctionDyn_iterate c (S.T v) (j' - j)
      rw [horbit, hlev, hlevv] at hdouble
      have hnorm : ‖v ^ (2 ^ (j' - j))‖ = ‖v'‖ := by
        rw [norm_pow]
        have hvpos : (0 : ℝ) < ‖v‖ := lt_trans (lt_trans zero_lt_one hrlo) hv.1
        have hv'pos : (0 : ℝ) < ‖v'‖ := lt_trans (lt_trans zero_lt_one hrlo) hv'.1
        have : Real.log (‖v‖ ^ (2 ^ (j' - j))) = Real.log ‖v'‖ := by
          rw [Real.log_pow]
          push_cast
          linarith [hdouble]
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
          (Set.mem_Ioi.mpr hv'pos) this
      rw [hnorm]
      exact hv'.2
  have htrans := tower_iterate_eq S hrlo (j' - j) hv hpow_mem
  rw [htrans] at horbit
  have hvv' : v ^ (2 ^ (j' - j)) = v' := S.inj hpow_mem hv' horbit
  rw [← hvv', ← pow_mul, ← pow_add]
  have harith : j' - j + (k - j') = k - j := by omega
  rw [harith]

end U0TowerData

namespace U0TowerData

/-- **The slit-gap plane geometry.**  A point whose angle from `c` is at least `θ₀` (encoded by
the inner-product bound) stays at distance `‖c‖·sin θ₀` from `c`, regardless of modulus.  This is
the consumable core of the quantitative slit gap: combined with a `‖T v − v‖ ≤ 1` proximity
clause on the anchor band, it yields `‖T v − c‖ ≥ ‖c‖·sin θ₀ − 1 > 1` for `‖c‖` large. -/
theorem norm_sub_ge_of_angle {v c : ℂ} {θ₀ : ℝ}
    (hang : (starRingEnd ℂ c * v).re ≤ Real.cos θ₀ * (‖c‖ * ‖v‖)) :
    ‖c‖ ^ (2 : ℕ) * Real.sin θ₀ ^ (2 : ℕ) ≤ ‖v - c‖ ^ (2 : ℕ) := by
  have hvc : ((starRingEnd ℂ c) * v).re = c.re * v.re + c.im * v.im := by
    simp [Complex.mul_re]
  have hexp : ‖v - c‖ ^ (2 : ℕ) = ‖v‖ ^ (2 : ℕ) + ‖c‖ ^ (2 : ℕ) - 2 * (c.re * v.re + c.im * v.im) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hs2 : Real.sin θ₀ ^ (2 : ℕ) = 1 - Real.cos θ₀ ^ (2 : ℕ) := by
    have := Real.sin_sq_add_cos_sq θ₀
    linarith
  rw [hvc] at hang
  rw [hexp, hs2]
  nlinarith [sq_nonneg (‖v‖ - Real.cos θ₀ * ‖c‖), norm_nonneg v, norm_nonneg c,
    Real.neg_one_le_cos θ₀, Real.cos_le_one θ₀, hang, sq_nonneg (Real.cos θ₀)]

end U0TowerData
