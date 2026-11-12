import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwinsContinuePastTheLine

/-!
# An odd zero of the edit exponential costs half its real part in the count

For an edit `e` of the rational primes write `E(s) = Σ_p e(p) p^{−s}`.  The Euler product is
`ζ_B(s) = ζ(s) exp(E(s) + E(2s)/2 + Q₃(s))`, where the third-order remainder
`Q₃(s) = Σ_p e(p)(−log(1 − p^{−s}) − p^{−s} − p^{−2s}/2)` is holomorphic on `Re s > θ/3` if the
edit is summable at `θ` (`editRem_eq`, `differentiableOn_editRem3_of_summable`).  So

  `((s − 1) ζ_B(s))² = ((s − 1) ζ(s) · e^{E(s)} · e^{Q₃(s)})² · e^{E(2s)}`:

the square of the zeta function sees the edit exponential at `2s` to the first power.

**Theorem** (`even_order_of_count`).  Let the edit be summable at `θ`, have count
`A x + O(x^β)`, and let `F` be a holomorphic continuation of `e^{E}` to `Re s > c₀`.  Then every
zero `ρ` of `F` with `Re ρ > 2 max(β, c₀, θ/3)` has even order.

Proof.  The count continues `(s − 1) ζ_B(s)` to `Re s > β`, so the identity holds on
`Re s > max(β, c₀, θ/3)`.  At `s₁ = ρ/2` the left side has even order, and the right side has
even order plus the order of `F` at `ρ` (`even_of_sq_eq_pow_mul`).

**Corollary** (`half_re_le_of_count_edit`).  The exponential of the greedy edit at a non-real
`ρ`, `1/2 < Re ρ < 13/15`, is `C (s − ρ)(s − ρ̄) e^{K(s)}` on a half-plane that contains `ρ/2`,
with a simple zero at `ρ`.  So every count exponent of the pair twin is at least `Re ρ/2`: its
zeta function has a square-root branch point at `ρ/2`.

A count below `x^{Re ρ/2}` for an edit with a simple fake zero at `ρ` is possible only if the
edit exponential itself is singular at `ρ/2`.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw

open PrimeEdits TwoSidedEdits

/-! ## The third-order remainder -/

/-- `r₃(z) = −log(1 − z) − z − z²/2`. -/
def logRem3 (z : ℂ) : ℂ := logRem z - z ^ 2 / 2

theorem norm_logRem3_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logRem3 z‖ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
  have h := Complex.norm_log_one_sub_inv_add_logTaylor_neg_le 2 hz
  have hmem : 1 + -z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one (by rwa [norm_neg])
  have hlog : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := by
    rw [sub_eq_add_neg]
    exact Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hmem)
  have hT : Complex.logTaylor (2 + 1) (-z) = -z - z ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  have heq : logRem3 z = Complex.log (1 - z)⁻¹ + Complex.logTaylor (2 + 1) (-z) := by
    rw [hlog, hT, logRem3, logRem]
    ring
  rw [heq]
  refine h.trans (le_of_eq ?_)
  norm_num

/-- The third-order remainder `Q₃(s) = Σ_p e(p) r₃(p^{−s})` of an edit. -/
def editRem3 (e : ℕ → ℤ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (e p : ℂ) * logRem3 (((p : ℕ) : ℂ) ^ (-s))

/-- The third-order remainder of an edit that is summable at `θ > 0` is holomorphic on
`Re s > θ/3`. -/
theorem differentiableOn_editRem3_of_summable {e : ℕ → ℤ} {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ)) :
    DifferentiableOn ℂ (editRem3 e) {s : ℂ | θ / 3 < s.re} := by
  have hUo : IsOpen {s : ℂ | θ / 3 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hq : (2 : ℝ) ^ (-(θ / 3)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hmaj : Summable fun p : Nat.Primes =>
      |(e p : ℝ)| * ((p : ℕ) : ℝ) ^ (-θ) * ((1 - (2 : ℝ) ^ (-(θ / 3)))⁻¹ / 3) :=
    (hS.subtype _).mul_right _
  refine differentiableOn_tsum_of_summable_norm hmaj (fun p => ?_) hUo (fun p w hw => ?_)
  · intro w hw
    have hw' : θ / 3 < w.re := hw
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hlt : ‖((p : ℕ) : ℂ) ^ (-(w + 0))‖ < 1 := by
      rw [norm_natCast_cpow_neg (p : ℕ) p.2.pos (w + 0)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
        (by simp only [add_zero]; linarith)
    have h := differentiableAt_logRem_cpow (n := (p : ℕ)) p.2.pos (c := 0) (s := w) hlt
    simp only [add_zero] at h
    have hpow : DifferentiableAt ℂ (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-s)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hp0)
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (e p : ℂ) * logRem3 (((p : ℕ) : ℂ) ^ (-s))) w := by
      unfold logRem3
      exact (h.sub ((hpow.pow 2).div_const 2)).const_mul _
    exact hd.differentiableWithinAt
  · have hw' : θ / 3 < w.re := hw
    have hz : ‖((p : ℕ) : ℂ) ^ (-w)‖ = ((p : ℕ) : ℝ) ^ (-w.re) :=
      norm_natCast_cpow_neg (p : ℕ) p.2.pos w
    have hzq : ‖((p : ℕ) : ℂ) ^ (-w)‖ ≤ (2 : ℝ) ^ (-(θ / 3)) := by
      rw [hz]; exact rpow_neg_le_two p.2.two_le (by linarith) hw'.le
    -- `|z|³ ≤ p^{−θ}` for `Re w ≥ θ/3`
    have hz3 : ‖((p : ℕ) : ℂ) ^ (-w)‖ ^ 3 ≤ ((p : ℕ) : ℝ) ^ (-θ) := by
      rw [hz]
      calc (((p : ℕ) : ℝ) ^ (-w.re)) ^ 3 ≤ (((p : ℕ) : ℝ) ^ (-(θ / 3))) ^ 3 :=
            pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (by linarith)) 3
        _ = ((p : ℕ) : ℝ) ^ (-θ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
            congr 1
            push_cast
            ring
    have h := norm_logRem3_le (hzq.trans_lt hq)
    have h1 : 0 < 1 - ‖((p : ℕ) : ℂ) ^ (-w)‖ := by linarith
    have h2 : (1 - ‖((p : ℕ) : ℂ) ^ (-w)‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-(θ / 3)))⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    have h5 := mul_le_mul hz3 h2 (inv_nonneg.mpr h1.le)
      (Real.rpow_nonneg (Nat.cast_nonneg ((p : ℕ))) (-θ))
    rw [norm_mul, Complex.norm_intCast]
    calc |(e p : ℝ)| * ‖logRem3 (((p : ℕ) : ℂ) ^ (-w))‖
        ≤ |(e p : ℝ)| * (((p : ℕ) : ℝ) ^ (-θ) * (1 - (2 : ℝ) ^ (-(θ / 3)))⁻¹ / 3) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |(e p : ℝ)| * ((p : ℕ) : ℝ) ^ (-θ) * ((1 - (2 : ℝ) ^ (-(θ / 3)))⁻¹ / 3) := by ring

/-- The prime-power remainder is half the edit series at `2s` plus the third-order remainder. -/
theorem editRem_eq {e : ℕ → ℤ} (he : IsEdit e) {s : ℂ} (hs : 1 < s.re) :
    editRem e s = LSeries (fun k => (e k : ℂ)) (2 * s) / 2 + editRem3 e s := by
  have h2re : (2 * s).re = 2 * s.re := by simp
  have hprime : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * s.re)) :=
    (Real.summable_nat_rpow.mpr (show -(2 * s.re) < -1 by linarith)).subtype _
  have hA : Summable fun p : Nat.Primes => (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-(2 * s)) :=
    Summable.of_norm_bounded hprime fun p => by
      rw [norm_mul, norm_natCast_cpow_neg _ p.2.pos, h2re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (he.norm_le_one p)
  have hB : Summable fun p : Nat.Primes => (e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s)) :=
    Summable.of_norm_bounded (summable_editMaj (a := 1) (by norm_num)) fun p =>
      norm_edit_mul_logRem_le he p (by norm_num) hs.le
  have hE : ∑' p : Nat.Primes, (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-(2 * s)) =
      LSeries (fun k => (e k : ℂ)) (2 * s) :=
    tsum_primes_eq_LSeries (fun k => (e k : ℂ)) (fun n hn => by simp [he.prime n hn]) (2 * s)
  have hterm : ∀ p : Nat.Primes, (e p : ℂ) * logRem3 (((p : ℕ) : ℂ) ^ (-s)) =
      (e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s)) -
        (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2 := fun p => by
    have hpow : (((p : ℕ) : ℂ) ^ (-s)) ^ 2 = ((p : ℕ) : ℂ) ^ (-(2 * s)) := by
      rw [← Complex.cpow_nat_mul]
      congr 1
      push_cast
      ring
    rw [logRem3, hpow]
    ring
  rw [editRem3, tsum_congr hterm, hB.tsum_sub (hA.div_const 2), tsum_div_const, hE, editRem]
  ring

/-! ## Parity of an order -/

/-- If `h² = (z − z₀)^m P² V` near `z₀` with `V(z₀) ≠ 0` and `P` not locally zero, then `m` is
even. -/
theorem even_of_sq_eq_pow_mul {h P V : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hh : AnalyticAt ℂ h z₀)
    (hP : AnalyticAt ℂ P z₀) (hV : AnalyticAt ℂ V z₀) (hV0 : V z₀ ≠ 0)
    (hPne : ¬ ∀ᶠ z in 𝓝 z₀, P z = 0)
    (heq : ∀ᶠ z in 𝓝 z₀, h z ^ 2 = (z - z₀) ^ m * (P z ^ 2 * V z)) : Even m := by
  have hh2 : AnalyticAt ℂ (fun z => h z ^ 2) z₀ := hh.pow 2
  obtain ⟨a, p, hpan, hp0, hpeq⟩ := hP.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hPne
  -- the order of `h²` is `m + 2a`
  have hord1 : analyticOrderAt (fun z => h z ^ 2) z₀ = ((m + 2 * a : ℕ) : ℕ∞) := by
    refine hh2.analyticOrderAt_eq_natCast.mpr ⟨fun z => p z ^ 2 * V z, (hpan.pow 2).mul hV,
      mul_ne_zero (pow_ne_zero 2 hp0) hV0, ?_⟩
    filter_upwards [heq, hpeq] with z hz hpz
    show h z ^ 2 = (z - z₀) ^ (m + 2 * a) • (p z ^ 2 * V z)
    rw [hz, hpz]
    simp only [smul_eq_mul]
    ring
  have hhne : ¬ ∀ᶠ z in 𝓝 z₀, h z = 0 := by
    intro hev
    have htop : analyticOrderAt (fun z => h z ^ 2) z₀ = ⊤ :=
      analyticOrderAt_eq_top.mpr (hev.mono fun z hz => by
        show h z ^ 2 = 0
        rw [hz]; norm_num)
    rw [hord1] at htop
    exact ENat.coe_ne_top _ htop
  -- and it is twice the order of `h`
  obtain ⟨n, q, hqan, hq0, hqeq⟩ := hh.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hhne
  have hord2 : analyticOrderAt (fun z => h z ^ 2) z₀ = ((2 * n : ℕ) : ℕ∞) := by
    refine hh2.analyticOrderAt_eq_natCast.mpr ⟨fun z => q z ^ 2, hqan.pow 2,
      pow_ne_zero 2 hq0, ?_⟩
    filter_upwards [hqeq] with z hz
    show h z ^ 2 = (z - z₀) ^ (2 * n) • q z ^ 2
    rw [hz]
    simp only [smul_eq_mul]
    ring
  have hnat : m + 2 * a = 2 * n := by
    have h3 := hord1.symm.trans hord2
    exact_mod_cast h3
  exact ⟨n - a, by omega⟩

/-! ## The count sees the edit exponential at `2s` -/

/-- Let an edit be summable at `θ`, have count `A x + O(x^β)`, and let `F` continue the edit
exponential to `Re s > c₀`.  At a point `s₁` right of `β`, `c₀` and `θ/3` the order of `F` at
`2 s₁` is even. -/
theorem even_order_at_two_mul_of_count {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ)) {A C β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    {c₀ : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hFeq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (fun k => (e k : ℂ)) s))
    {s₁ : ℂ} {m : ℕ} (hm : analyticOrderAt F (2 * s₁) = m)
    (h1 : β < s₁.re) (h2 : c₀ < s₁.re) (h3 : θ / 3 < s₁.re) : Even m := by
  obtain ⟨G, hG, hGeq⟩ := exists_continuation_of_count (hasIntegerNorms_editSystem e)
    (isDiscrete_editSystem e) hβ hβ1 hN
  have hQ := differentiableOn_editRem3_of_summable hθ hS
  -- the half-plane of the identity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max β (max c₀ (θ / 3)) := ⟨_, rfl⟩
  have hcβ : β ≤ c := by rw [hc]; exact le_max_left _ _
  have hc₀ : c₀ ≤ c := by rw [hc]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hcθ : θ / 3 ≤ c := by rw [hc]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcs : c < s₁.re := by rw [hc]; exact max_lt h1 (max_lt h2 h3)
  have hUo : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs₁ : s₁ ∈ {s : ℂ | c < s.re} := hcs
  have h2re : ∀ s : ℂ, (2 * s).re = 2 * s.re := fun s => by simp
  have hGc : DifferentiableOn ℂ G {s : ℂ | c < s.re} :=
    hG.mono fun s (hs : c < s.re) => show β < s.re from lt_of_le_of_lt hcβ hs
  have hFc : DifferentiableOn ℂ F {s : ℂ | c < s.re} :=
    hF.mono fun s (hs : c < s.re) => show c₀ < s.re from lt_of_le_of_lt hc₀ hs
  have hQc : DifferentiableOn ℂ (editRem3 e) {s : ℂ | c < s.re} :=
    hQ.mono fun s (hs : c < s.re) => show θ / 3 < s.re from lt_of_le_of_lt hcθ hs
  have hF2 : DifferentiableOn ℂ (fun s : ℂ => F (2 * s)) {s : ℂ | c < s.re} :=
    hF.comp (differentiable_id.const_mul (2 : ℂ)).differentiableOn
      fun s (hs : c < s.re) => by
        show c₀ < (2 * s).re
        rw [h2re]
        have hs0 : 0 < s.re := by linarith
        linarith [lt_of_le_of_lt hc₀ hs]
  have hP : DifferentiableOn ℂ
      (fun s : ℂ => zetaResidueUnit s * F s * Complex.exp (editRem3 e s))
      {s : ℂ | c < s.re} :=
    (differentiable_zetaResidueUnit.differentiableOn.mul hFc).mul hQc.cexp
  -- the identity on `Re s > 1`
  have hagree : ∀ s : ℂ, 1 < s.re → G s ^ 2 =
      (zetaResidueUnit s * F s * Complex.exp (editRem3 e s)) ^ 2 * F (2 * s) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have h2s : 1 < (2 * s).re := by rw [h2re]; linarith
    rw [hGeq s hs, editSystem_zetaSeriesC he hs, editRem_eq he hs, hFeq s hs,
      hFeq (2 * s) h2s, zetaResidueUnit_of_ne hs1]
    generalize LSeries (fun k => (e k : ℂ)) s = a
    generalize LSeries (fun k => (e k : ℂ)) (2 * s) = b
    generalize editRem3 e s = q
    rw [show cexp (a + (b / 2 + q)) = cexp a * cexp q * cexp (b / 2) by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring]
    have hb : cexp (b / 2) ^ 2 = cexp b := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    linear_combination ((s - 1) * riemannZeta s * cexp a * cexp q) ^ 2 * hb
  -- and on the half-plane
  have hon := eqOn_halfPlane (c := c) (F₁ := fun s => G s ^ 2)
    (F₂ := fun s => (zetaResidueUnit s * F s * Complex.exp (editRem3 e s)) ^ 2 * F (2 * s))
    (hGc.pow 2) ((hP.pow 2).mul hF2) hagree
  have hEq : ∀ s : ℂ, c < s.re → G s ^ 2 =
      (zetaResidueUnit s * F s * Complex.exp (editRem3 e s)) ^ 2 * F (2 * s) :=
    fun s hs => hon hs
  -- the local form of `F` at `2 s₁`
  have hρmem : (2 * s₁) ∈ {s : ℂ | c₀ < s.re} := by
    show c₀ < (2 * s₁).re
    rw [h2re]
    linarith
  have hU₀ : IsOpen {s : ℂ | c₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hFan : AnalyticAt ℂ F (2 * s₁) := hF.analyticAt (hU₀.mem_nhds hρmem)
  obtain ⟨f, hfan, hf0, hfeq⟩ := hFan.analyticOrderAt_eq_natCast.mp hm
  have htend : Tendsto (fun s : ℂ => 2 * s) (𝓝 s₁) (𝓝 (2 * s₁)) :=
    (continuous_const.mul continuous_id).tendsto s₁
  have hF2eq : ∀ᶠ s in 𝓝 s₁, F (2 * s) = (2 * s - 2 * s₁) ^ m • f (2 * s) :=
    htend.eventually hfeq
  have hGan : AnalyticAt ℂ G s₁ := hGc.analyticAt (hUo.mem_nhds hs₁)
  have hPan : AnalyticAt ℂ
      (fun s : ℂ => zetaResidueUnit s * F s * Complex.exp (editRem3 e s)) s₁ :=
    hP.analyticAt (hUo.mem_nhds hs₁)
  have hinner : AnalyticAt ℂ (fun s : ℂ => 2 * s) s₁ := analyticAt_const.mul analyticAt_id
  have hVan : AnalyticAt ℂ (fun s : ℂ => (2 : ℂ) ^ m * f (2 * s)) s₁ :=
    analyticAt_const.mul (hfan.comp_of_eq hinner rfl)
  have hV0 : (2 : ℂ) ^ m * f (2 * s₁) ≠ 0 := mul_ne_zero (pow_ne_zero m two_ne_zero) hf0
  -- the square factor is not locally zero: otherwise `(s − 1) ζ_B(s)` vanishes identically
  have hPne : ¬ ∀ᶠ s in 𝓝 s₁, zetaResidueUnit s * F s * Complex.exp (editRem3 e s) = 0 := by
    intro hev
    have hG0 : ∀ᶠ s in 𝓝 s₁, G s = 0 := by
      filter_upwards [hUo.mem_nhds hs₁, hev] with s hsU hPs
      have h := hEq s hsU
      rw [hPs, zero_pow two_ne_zero, zero_mul] at h
      exact (pow_eq_zero_iff two_ne_zero).mp h
    have hUβ : IsOpen {s : ℂ | β < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hglob := (hG.analyticOnNhd hUβ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt β).isPreconnected (show s₁ ∈ {s : ℂ | β < s.re} from h1) hG0
    have h2re' : (2 : ℂ).re = 2 := by norm_num
    have h2 : G 2 = 0 := hglob (show β < (2 : ℂ).re by rw [h2re']; linarith)
    rw [hGeq 2 (by rw [h2re']; norm_num),
      editSystem_zetaSeriesC he (by rw [h2re']; norm_num)] at h2
    exact mul_ne_zero (by norm_num) (mul_ne_zero
      (riemannZeta_ne_zero_of_one_lt_re (by rw [h2re']; norm_num)) (Complex.exp_ne_zero _)) h2
  -- the local factorization of the square
  have heq : ∀ᶠ s in 𝓝 s₁, G s ^ 2 = (s - s₁) ^ m *
      ((zetaResidueUnit s * F s * Complex.exp (editRem3 e s)) ^ 2 *
        ((2 : ℂ) ^ m * f (2 * s))) := by
    filter_upwards [hUo.mem_nhds hs₁, hF2eq] with s hsU hFs
    have hpow : (2 * s - 2 * s₁) ^ m = (2 : ℂ) ^ m * (s - s₁) ^ m := by
      rw [← mul_sub, mul_pow]
    rw [hEq s hsU, hFs, smul_eq_mul, hpow]
    ring
  exact even_of_sq_eq_pow_mul hGan hPan hVan hV0 hPne heq

/-- **Zeros of the edit exponential beyond twice the count exponent have even order.**  Let an
edit be summable at `θ`, have count `A x + O(x^β)`, and let `F` continue the edit exponential
to `Re s > c₀`.  A zero `ρ` of `F` with `Re ρ > 2 max(β, c₀, θ/3)` has even order. -/
theorem even_order_of_count {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ)) {A C β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    {c₀ : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hFeq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (fun k => (e k : ℂ)) s))
    {ρ : ℂ} {m : ℕ} (hm : analyticOrderAt F ρ = m)
    (h1 : 2 * β < ρ.re) (h2 : 2 * c₀ < ρ.re) (h3 : 2 * θ / 3 < ρ.re) : Even m := by
  have hρ : (2 : ℂ) * (ρ / 2) = ρ := by ring
  have hre : (ρ / 2).re = ρ.re / 2 := by simp
  exact even_order_at_two_mul_of_count he hθ hS hβ hβ1 hN hF hFeq (s₁ := ρ / 2)
    (by rw [hρ]; exact hm) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [hre]; linarith)

/-! ## The pair twin -/

/-- **The count exponent of a pair twin is at least half its top.**  For a non-real `ρ` with
`1/2 < Re ρ < 13/15`, every count exponent `β` of the greedy edit at `ρ` has `β ≥ Re ρ/2`. -/
theorem half_re_le_of_count_edit {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 13 / 15)
    (him : ρ.im ≠ 0) {A C β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem (edit ρ)).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ρ.re / 2 ≤ β := by
  by_contra hlt
  have hβρ : β < ρ.re / 2 := not_le.mp hlt
  -- a half-plane `Re s > c₀` with `Re ρ − 13/30 < c₀ < Re ρ/2`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = (ρ.re - 13 / 30 + ρ.re / 2) / 2 := ⟨_, rfl⟩
  have hc₀1 : ρ.re - 13 / 30 < c₀ := by rw [hc₀]; linarith
  have hc₀2 : c₀ < ρ.re / 2 := by rw [hc₀]; linarith
  have hc₀0 : 0 < c₀ := by linarith
  -- the discrepancy of the greedy edit is `O(n^{c₀})`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (17 / 30 + (c₀ + (1 - ρ.re))) / 2 := ⟨_, rfl⟩
  have hα0 : 17 / 30 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαc : α - (1 - ρ.re) ≤ c₀ := by rw [hα]; linarith
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  have hm : ∀ k : ℕ, 1 ≤ k → |target ρ k| ≤ 2 * (k : ℝ) ^ (-(1 - ρ.re)) := fun k hk => by
    have h := abs_target_le ρ hk
    rwa [show ρ.re - 1 = -(1 - ρ.re) by ring] at h
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_le_rpow_of_abs_le (m := target ρ) (A := 2)
    (η := 1 - ρ.re) (c := c₀) (by norm_num) (by linarith) (by linarith) hm hα1 hc₀0 hαc hwin
  have hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (target ρ k : ℂ)) s := by
    intro s hs
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1 - (1 - ρ.re)) (by linarith)
      ⟨2, fun n hn => ?_⟩
    show ‖((target ρ n : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, show 1 - (1 - ρ.re) - 1 = -(1 - ρ.re) by ring]
    exact hm n (Nat.one_le_iff_ne_zero.mpr hn)
  obtain ⟨C₁, K, hC₁, hK, hfac⟩ := exists_exp_geditSeries_eq (m := target ρ)
    (target_zero (by linarith)) hK₀ hc₀0 (by linarith) hdisc hsumm
    (L := fun s => (s - ρ) * (s - (starRingEnd ℂ) ρ))
    (Φ₀ := fun s => PrimeEdits.zetaRegular (s - (ρ - 1)) +
      PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) ρ - 1)))
    ((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
      (PrimeEdits.differentiable_zetaRegular.comp
        (differentiable_id.sub_const _))).differentiableOn
    (fun s hs => logDeriv_pair_eq (by linarith) hs)
  -- the continuation of the edit exponential and its simple zero at `ρ`
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ,
      F = fun s => C₁ * ((s - ρ) * (s - (starRingEnd ℂ) ρ)) * Complex.exp (K s) := ⟨_, rfl⟩
  have hU₀ : IsOpen {s : ℂ | c₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re} := by
    rw [hFdef]
    exact ((differentiableOn_const C₁).mul ((differentiableOn_id.sub_const ρ).mul
      (differentiableOn_id.sub_const _))).mul hK.cexp
  have hFeq : ∀ s : ℂ, 1 < s.re →
      F s = Complex.exp (LSeries (fun k => (edit ρ k : ℂ)) s) := fun s hs => by
    rw [hFdef]
    exact (hfac s hs).symm
  have hρmem : ρ ∈ {s : ℂ | c₀ < s.re} := show c₀ < ρ.re by linarith
  have hfan : AnalyticAt ℂ
      (fun s : ℂ => C₁ * (s - (starRingEnd ℂ) ρ) * Complex.exp (K s)) ρ := by
    have hd : DifferentiableOn ℂ
        (fun s : ℂ => C₁ * (s - (starRingEnd ℂ) ρ) * Complex.exp (K s))
        {s : ℂ | c₀ < s.re} :=
      ((differentiableOn_const C₁).mul (differentiableOn_id.sub_const _)).mul hK.cexp
    exact hd.analyticAt (hU₀.mem_nhds hρmem)
  have hne : ρ - (starRingEnd ℂ) ρ ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h'
    exact him (by linarith)
  have hord : analyticOrderAt F ρ = ((1 : ℕ) : ℕ∞) := by
    refine (hF.analyticAt (hU₀.mem_nhds hρmem)).analyticOrderAt_eq_natCast.mpr
      ⟨_, hfan, mul_ne_zero (mul_ne_zero hC₁ hne) (Complex.exp_ne_zero _),
        Filter.Eventually.of_forall fun s => ?_⟩
    rw [hFdef]
    show C₁ * ((s - ρ) * (s - (starRingEnd ℂ) ρ)) * Complex.exp (K s) =
      (s - ρ) ^ 1 • (C₁ * (s - (starRingEnd ℂ) ρ) * Complex.exp (K s))
    rw [pow_one, smul_eq_mul]
    ring
  -- the edit is summable at `5 Re ρ/4`, and `5 Re ρ/12 < Re ρ/2`
  have hS := summable_abs_edit_rpow (ρ := ρ) (σ := 5 * ρ.re / 4) (by linarith) (by linarith)
    (by linarith)
  have heven := even_order_of_count (isEdit_edit ρ) (θ := 5 * ρ.re / 4) (by linarith) hS hβ
    (by linarith) hN hF hFeq hord (by linarith) (by linarith) (by linarith)
  exact absurd heven (by decide)

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw
