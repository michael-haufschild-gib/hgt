import GaloisForLFunctions.FiniteFreeProbability.SymmetrizedEulerHorizon
import GaloisForLFunctions.FiniteFreeProbability.ShiftRegimeGaussianCapacity
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteEdgeAsymptotics
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit

/-!
# The degree horizon of a curved phase

A linear phase `e^{iδw}` translates reversed Jensen roots by `−iδ`. A curved phase `e^{iaw²}`
(`a > 0`) acts as the imaginary heat flow `e^{iaD²}`: with `σ = √a (1 − i)`, `σ² = −2ia`,

`R_d(e^{iaw²})(y) = σ^d He_d(y/σ)`,

so its roots are `σh`, `h` running over the (real) zeros of the Hermite polynomial `He_d`: half of
them lie in the upper half-plane. Hence the roots of `R_d(e^{iδw + iaw²})` are `σh − iδ`, with
imaginary parts `−√a h − δ`.

**Theorem.** `R_{n+1}(e^{iδw + iaw²})` has all roots in the open lower half-plane iff
`√a · h_max < δ`, `h_max` the largest zero of `He_{n+1}`. Since `h_max < 2√(n+1)` and
`h_max²/(n+1) → 4`, a phase with drift `δ` and curvature `a` is Hermite–Biehler stable up to
degree `≈ δ²/(4a)` and unstable beyond it.

With an Euler product (Walsh): if `√a h_max ≤ c − θ_S/2` then `e^{icw + iaw²}Π_{p∈S}(1 − p^{−σ−iw})`
is stable at degree `n + 1`. For the Gamma phase `θ(t + w)` at height `t` (drift `θ'(t)`,
curvature `θ''(t)/2`) this is the local finite free horizon: the carrier condition
`θ_S/2 < θ'(t)` together with a degree bound of order `(θ'(t) − θ_S/2)²/θ''(t)`.
-/

open Polynomial Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-! ## The complex heat flow of `X^d` -/

/-- The complex Gaussian `e^{sw²}` as a power series. -/
def gaussC (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => if 2 ∣ k then s ^ (k / 2) / ((k / 2).factorial : ℂ) else 0

theorem coeff_heatSymbol_complex (s : ℂ) {d n : ℕ} (hn : n ≤ d) :
    (heatSymbol s d).coeff n = if 2 ∣ n then s ^ (n / 2) / ((n / 2).factorial : ℂ) else 0 := by
  rw [heatSymbol, finsetSum_coeff]
  split_ifs with h2
  · obtain ⟨m, rfl⟩ := h2
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro hm; exact absurd (Finset.mem_range.2 (by omega)) hm
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => h2 ⟨k, h⟩), mul_zero]

/-- `R_d(e^{sw²}) = e^{sD²}X^d`. -/
theorem jensenRev_gaussC (s : ℂ) (d : ℕ) : jensenRev d (gaussC s) = heatOp s d (X ^ d) := by
  rw [jensenRev, heatOp]
  refine diffOp_congr (natDegree_X_pow_le d) fun i hi => ?_
  rw [PowerSeries.coeff_trunc, if_pos (by omega), gaussC, PowerSeries.coeff_mk,
    coeff_heatSymbol_complex s hi]

theorem eval_heatOp_X_pow (s y : ℂ) (d : ℕ) :
    (heatOp s d (X ^ d)).eval y = ∑ k ∈ Finset.range (d + 1),
      s ^ k / (k.factorial : ℂ) * (d.descFactorial (2 * k) : ℂ) * y ^ (d - 2 * k) := by
  rw [heatOp_eq_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- **Scaling.** If `σ² = −2s`, then `e^{sD²}X^d` at `y` is `σ^d He_d(y/σ)`. -/
theorem eval_heatOp_X_pow_scale {s σ : ℂ} (hσ : σ ≠ 0) (hs : σ ^ 2 = -2 * s) (d : ℕ) (y : ℂ) :
    (heatOp s d (X ^ d)).eval y = σ ^ d * (heatOp (-(1 / 2)) d (X ^ d)).eval (y / σ) := by
  rw [eval_heatOp_X_pow, eval_heatOp_X_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h2k : 2 * k ≤ d
  · have hσd : σ ^ d = (-2 * s) ^ k * σ ^ (d - 2 * k) := by
      rw [← hs, ← pow_mul, ← pow_add, Nat.add_sub_cancel' h2k]
    have hsk : (-2 * s) ^ k * (-(1 / 2) : ℂ) ^ k = s ^ k := by
      rw [← mul_pow]; congr 1; ring
    have hy : σ ^ (d - 2 * k) * (y / σ) ^ (d - 2 * k) = y ^ (d - 2 * k) := by
      rw [← mul_pow, mul_div_cancel₀ y hσ]
    calc s ^ k / (k.factorial : ℂ) * (d.descFactorial (2 * k) : ℂ) * y ^ (d - 2 * k)
        = ((-2 * s) ^ k * (-(1 / 2) : ℂ) ^ k) / (k.factorial : ℂ) * (d.descFactorial (2 * k) : ℂ) *
            (σ ^ (d - 2 * k) * (y / σ) ^ (d - 2 * k)) := by rw [hsk, hy]
      _ = _ := by rw [hσd]; ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; simp

/-- The complex lift of the Hermite polynomial. -/
theorem heatOp_neg_half_eq_map (d : ℕ) :
    heatOp (-(1 / 2) : ℂ) d (X ^ d) = (hermiteReal d).map (algebraMap ℝ ℂ) := by
  rw [hermiteReal_eq_heatOp, heatOp_map]
  simp

theorem hermiteReal_ne_zero (d : ℕ) : hermiteReal d ≠ 0 := by
  intro h
  have := coeff_hermiteFF_self (-(1 / 2)) d
  rw [hermiteFF, ← hermiteReal_eq_heatOp, h, coeff_zero] at this
  exact zero_ne_one this

/-! ## Roots of the quadratic phase -/

/-- The rotation `σ = √a (1 − i)`, `σ² = −2ia`. -/
def phaseRotation (a : ℝ) : ℂ := (Real.sqrt a : ℂ) * (1 - I)

theorem phaseRotation_sq {a : ℝ} (ha : 0 ≤ a) : phaseRotation a ^ 2 = -2 * (I * a) := by
  have h : ((Real.sqrt a : ℝ) : ℂ) ^ 2 = (a : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ha]
  rw [phaseRotation, mul_pow, h]
  ring_nf; rw [I_sq]; ring

theorem phaseRotation_ne_zero {a : ℝ} (ha : 0 < a) : phaseRotation a ≠ 0 := by
  rw [phaseRotation]
  refine mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 ha).ne') ?_
  intro h; have := congrArg Complex.re h; simp at this

/-- **The roots of `R_d(e^{iδw + iaw²})` are `σh − iδ`, `He_d(h) = 0`.** -/
theorem isRoot_quadraticPhase_iff {a : ℝ} (ha : 0 < a) (δ : ℝ) (d : ℕ) (x : ℂ) :
    (jensenRev d (expSeries (I * δ) * gaussC (I * a))).IsRoot x ↔
      ∃ h : ℝ, (hermiteReal d).IsRoot h ∧ x = phaseRotation a * h - I * δ := by
  have hσ := phaseRotation_ne_zero ha
  rw [jensenRev_expSeries_mul, jensenRev_gaussC, IsRoot, eval_comp, eval_add, eval_X, eval_C,
    eval_heatOp_X_pow_scale hσ (phaseRotation_sq ha.le), heatOp_neg_half_eq_map]
  constructor
  · intro hx
    have hz : ((hermiteReal d).map (algebraMap ℝ ℂ)).eval ((x + I * δ) / phaseRotation a) = 0 :=
      (mul_eq_zero.1 hx).resolve_left (pow_ne_zero _ hσ)
    have him := im_eq_zero_of_splits (splits_hermiteReal d) (hermiteReal_ne_zero d)
      (z := (x + I * δ) / phaseRotation a) (by rwa [aeval_def, eval₂_eq_eval_map])
    set z := (x + I * δ) / phaseRotation a
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    refine ⟨z.re, ?_, ?_⟩
    · rw [hzre, eval_map, show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl,
        eval₂_at_apply] at hz
      exact (algebraMap ℝ ℂ).injective (by rw [hz, map_zero])
    · rw [← hzre]; simp only [z]; field_simp; ring
  · rintro ⟨h, hh, rfl⟩
    rw [show phaseRotation a * h - I * δ + I * δ = phaseRotation a * h by ring,
      mul_div_cancel_left₀ _ hσ, eval_map, show ((h : ℝ) : ℂ) = algebraMap ℝ ℂ h from rfl,
      eval₂_at_apply, hh.eq_zero, map_zero, mul_zero]

theorem im_phaseRotation_mul (a h : ℝ) (δ : ℝ) :
    (phaseRotation a * h - I * δ).im = -(Real.sqrt a * h) - δ := by
  simp [phaseRotation, Complex.mul_im, Complex.mul_re]

/-- **Exact stability window of a curved phase.** `R_{n+1}(e^{iδw + iaw²})` has all roots in the open
lower half-plane iff `√a · h_max < δ`, `h_max` the largest zero of `He_{n+1}`. -/
theorem quadraticPhase_stable_iff {a : ℝ} (ha : 0 < a) (δ : ℝ) (n : ℕ) :
    (∀ x : ℂ, (jensenRev (n + 1) (expSeries (I * δ) * gaussC (I * a))).IsRoot x → x.im < 0) ↔
      Real.sqrt a * GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge n < δ := by
  set e := GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge n
  have hneg : (hermiteReal (n + 1)).IsRoot (-e) := by
    rw [IsRoot, eval_neg_hermiteReal,
      GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge_isRoot, mul_zero]
  constructor
  · intro hst
    have := hst _ ((isRoot_quadraticPhase_iff ha δ (n + 1) _).2 ⟨-e, hneg, rfl⟩)
    rw [im_phaseRotation_mul] at this
    linarith
  · intro hlt x hx
    obtain ⟨h, hh, rfl⟩ := (isRoot_quadraticPhase_iff ha δ (n + 1) x).1 hx
    have hmh : -h ≤ e := GaloisForLFunctions.ArithmeticLocalDivisorGeometry.le_hermiteEdge_of_root n
      (by rw [eval_neg_hermiteReal, hh.eq_zero, mul_zero])
    rw [im_phaseRotation_mul]
    nlinarith [Real.sqrt_nonneg a]

/-- Stable up to degree `δ²/(4a)`: if `2√(a(n+1)) ≤ δ`, every root lies in `Im < 0`. -/
theorem quadraticPhase_stable_of_le {a : ℝ} (ha : 0 < a) {δ : ℝ} {n : ℕ}
    (h : 2 * Real.sqrt (a * (n + 1)) ≤ δ) :
    ∀ x : ℂ, (jensenRev (n + 1) (expSeries (I * δ) * gaussC (I * a))).IsRoot x → x.im < 0 := by
  refine (quadraticPhase_stable_iff ha δ n).2 (lt_of_lt_of_le ?_ h)
  have he := GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge_lt_two_sqrt n
  rw [Real.sqrt_mul ha.le, show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at *
  have hsa := Real.sqrt_pos.2 ha
  nlinarith

/-- **Every curved phase has a finite degree horizon.** -/
theorem eventually_not_stable_quadraticPhase {a : ℝ} (ha : 0 < a) (δ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ¬ ∀ x : ℂ,
      (jensenRev (n + 1) (expSeries (I * δ) * gaussC (I * a))).IsRoot x → x.im < 0 := by
  have hlim := GaloisForLFunctions.ArithmeticLocalDivisorGeometry.tendsto_hermiteEdge_sq_div_degree
  have h1 := hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 4))
  have h2 : ∀ᶠ n : ℕ in atTop, δ ^ 2 / a ≤ (n : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop _
  filter_upwards [h1, h2] with n hn hn2
  rw [quadraticPhase_stable_iff ha δ n, not_lt]
  set e := GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge n
  have he0 : 0 ≤ e := GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge_nonneg n
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [lt_div_iff₀ hpos, one_mul] at hn
  rcases le_or_gt δ 0 with hδ | hδ
  · exact hδ.trans (mul_nonneg (Real.sqrt_nonneg a) he0)
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have hsq : (Real.sqrt a * e) ^ 2 ≥ δ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha.le]
      rw [div_le_iff₀ ha] at hn2
      nlinarith
    nlinarith [mul_nonneg hsa.le he0]

/-! ## Curved phase times a finite Euler product -/

/-- **Walsh with a curved phase.** If `√a · h_max ≤ c − θ_S/2`, the reversed Jensen polynomial of
degree `n + 1` of `e^{icw + iaw²}Π_{p∈S}(1 − p^{−σ−iw})` has all roots in the open lower
half-plane. -/
theorem im_neg_of_isRoot_jensenRev_gaussC_mul_translatedMobiusProduct {S : Finset Nat.Primes}
    (hS : S.Nonempty) {σ : ℝ} (hσ : 0 < σ) {a : ℝ} (ha : 0 < a) {c : ℝ} {n : ℕ}
    (hc : Real.sqrt a * GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge n ≤
      c - logFrequency S / 2) {x : ℂ}
    (hx : (jensenRev (n + 1) (gaussC (I * a) * translatedMobiusProduct S σ c)).IsRoot x) :
    x.im < 0 := by
  classical
  set δ := c - logFrequency S / 2
  set E := eulerProduct S (fun p => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ))
    fun p => Real.log ((p : ℕ) : ℝ)
  have hsplit : gaussC (I * a) * translatedMobiusProduct S σ c =
      (expSeries (I * δ) * gaussC (I * a)) * E := by
    rw [translatedMobiusProduct_eq_expSeries_mul]
    simp only [δ, E]; push_cast; ring
  rw [hsplit, jensenRev_mul, ffConv_comm (natDegree_jensenRev_le _ _)
    (natDegree_jensenRev_le _ _)] at hx
  have hqlt : ∀ p ∈ S, ‖((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖ < 1 := fun p _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hcE := constantCoeff_eulerProduct_ne_zero S _ (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ))
    hqlt
  have hcG : PowerSeries.constantCoeff (expSeries (I * δ) * gaussC (I * a)) ≠ 0 := by
    rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, expSeries, gaussC, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk]
    simp
  have hroots := (roots_jensenRev_eulerProduct (fun p : Nat.Primes => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ))
    (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) (by omega : 1 ≤ n + 1) S hqlt
    (fun p _ => Real.log_pos (by exact_mod_cast p.prop.one_lt))).2 hS
  have hq : ∀ μ, (jensenRev (n + 1) (expSeries (I * δ) * gaussC (I * a))).IsRoot μ →
      μ.im ≤ Real.sqrt a * GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge n - δ := by
    intro μ hμ
    obtain ⟨h, hh, rfl⟩ := (isRoot_quadraticPhase_iff ha δ (n + 1) μ).1 hμ
    have hmh : -h ≤ GaloisForLFunctions.ArithmeticLocalDivisorGeometry.hermiteEdge n :=
      GaloisForLFunctions.ArithmeticLocalDivisorGeometry.le_hermiteEdge_of_root n
        (by rw [eval_neg_hermiteReal, hh.eq_zero, mul_zero])
    rw [im_phaseRotation_mul]
    nlinarith [Real.sqrt_nonneg a]
  have := ffConv_root_im_lt (jensenRev_ne_zero hcE) (natDegree_jensenRev hcE)
    (jensenRev_ne_zero hcG) (natDegree_jensenRev_le _ _) hroots hq hx
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.quadraticPhase_stable_iff
#print axioms FiniteFreeProbability.eventually_not_stable_quadraticPhase
#print axioms FiniteFreeProbability.im_neg_of_isRoot_jensenRev_gaussC_mul_translatedMobiusProduct
