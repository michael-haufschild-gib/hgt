import GaloisForLFunctions.RHTower.DeBruijnNewmanCosineShift
import GaloisForLFunctions.RHTower.RiemannKernelEdgeProfile
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeDeBruijnNewman
import GaloisForLFunctions.RHTower.XiCosineShiftNonrealZeroCount

/-!
# Only the undeformed Riemann kernel has a Dirichlet series

The heat family `Φ(x) e^{−τx²}` (`H_{−τ}`, de Bruijn–Newman time `−τ`) shares every size property of
`Φ`; an input that singles out `τ = 0` has to be arithmetic. The weakest one already does: the
Dirichlet series. Write `s = σ` real and

`ξ_τ(σ) = H_{−τ}(i(½ − σ)) = ∫ Φ(x) e^{−τx²} e^{(σ−½)x} dx`    (`riemannHeat_neg_eq_heatLaplace`).

* **Tilted law** (`heatLaplace_le`, `heatLaplace_ge`, `heatLaplace_ge_of_nonpos`). Under the
  probability law `∝ Φ(x) e^{cx} dx` the ratio `R_τ(c) = ξ_τ/ξ_0` is the mean of `e^{−τx²}`. The law
  escapes to `+∞` but stays below `log(2c + 6)` (the envelope `Φ ≤ C₀ e^{9x/2} e^{−πe^{2x}}`), so
  for `τ > 0`: `R_τ(c) → 0` and `R_τ(c) ≥ ½ e^{−τ log(2c+6)²}` eventually; for `τ < 0`:
  `R_τ(c) → ∞` (`tendsto_ratio_zero`, `eventually_ratio_ge`, `tendsto_ratio_atTop`).
* **Dirichlet series** (`norm_LSeries_sub_le`). An absolutely convergent `D(σ) = Σ a_n n^{-σ}` has
  `|D(σ) − a₁| ≤ 2^{σ₁−σ} Σ_n |a_n| n^{−σ₁}`: it tends to `a₁` and, if `a₁ = 0`, decays
  exponentially.
* **The selector** (`exists_dirichlet_iff`). `ξ_τ(s) = ½s(s−1)Γ_ℝ(s) D(s)` on a real half-line for
  some absolutely convergent Dirichlet series `D` iff `τ = 0`. Since `ξ_τ/ξ = D/ζ`: for `τ > 0` it
  would force `a₁ = 0` and then an exponentially small `D` against the lower bound
  `e^{−τ log(2σ+5)²}`; for `τ < 0` a bounded `D` against `R_τ → ∞`.

So among `Φe^{−τx²}` the Dirichlet structure alone, with no Euler product and no functional
equation, selects `τ = 0`; it is read on the real axis at `σ → ∞`, at the scale `log σ` of the
tilted law, far from every zero.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open _root_.RHTower _root_.RHTower.DeBruijn

/-! ### The tilted Laplace transform -/

/-- `L_τ(c) = ∫ Φ(x) e^{−τx²} e^{cx} dx`. -/
def heatLaplace (τ c : ℝ) : ℝ :=
  ∫ x, riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x)

theorem continuous_heatIntegrand (τ c : ℝ) :
    Continuous fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x) :=
  (continuous_riemannKernelReal.mul (by fun_prop)).mul (by fun_prop)

theorem integrable_heatIntegrand (τ c : ℝ) :
    Integrable fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x) := by
  have h := FiniteFreeProbability.integrable_heatEnvelope (t := max (-τ) 0) (le_max_right _ _) |c|
  refine h.mono' (continuous_heatIntegrand τ c).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hΦ := (riemannKernelReal_pos x).le
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : Real.exp (-τ * x ^ 2) ≤ Real.exp (max (-τ) 0 * x ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg x))
  have h2 : Real.exp (c * x) ≤ Real.exp (|x| * |c|) := by
    refine Real.exp_le_exp.mpr ?_
    calc c * x ≤ |c * x| := le_abs_self _
      _ = |x| * |c| := by rw [abs_mul, mul_comm]
  calc riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x)
      = riemannKernelReal x * (Real.exp (-τ * x ^ 2) * Real.exp (c * x)) := by ring
    _ ≤ riemannKernelReal x * (Real.exp (max (-τ) 0 * x ^ 2) * Real.exp (|x| * |c|)) := by
        gcongr

theorem integrable_riemannKernelReal' : Integrable riemannKernelReal :=
  (integrable_heatIntegrand 0 0).congr (Eventually.of_forall fun x => by simp)

theorem integrable_exp_neg_abs' : Integrable fun x : ℝ => Real.exp (-|x|) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic one_pos 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (mem_Iic.mp hx), neg_neg, one_mul]
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).congr_fun (fun x hx => ?_)
      measurableSet_Ioi
    simp only [abs_of_pos (mem_Ioi.mp hx), neg_mul, one_mul]
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem heatIntegrand_zero (c x : ℝ) :
    riemannKernelReal x * Real.exp (-0 * x ^ 2) * Real.exp (c * x) =
      riemannKernelReal x * Real.exp (c * x) := by
  simp

theorem heatLaplace_nonneg (τ c : ℝ) : 0 ≤ heatLaplace τ c :=
  integral_nonneg fun x => by have := (riemannKernelReal_pos x).le; positivity

/-- `ξ_τ(σ) = L_τ(σ − ½)` on the real axis. -/
theorem riemannHeat_neg_eq_heatLaplace (τ σ : ℝ) :
    riemannHeat (-τ) (((1 / 2 - σ : ℝ) : ℂ) * I) = (heatLaplace τ (σ - 1 / 2) : ℂ) := by
  rw [riemannHeat_neg_ofReal_mul_I]
  congr 1
  unfold heatLaplace
  congr 1
  funext x
  rw [show -(1 / 2 - σ) * x = (σ - 1 / 2) * x by ring]

/-- `ξ(σ) = L_0(σ − ½)`. -/
theorem xi_eq_heatLaplace (σ : ℝ) : xi σ = (heatLaplace 0 (σ - 1 / 2) : ℂ) := by
  rw [← riemannHeat_neg_eq_heatLaplace, neg_zero, riemannHeat_zero]
  congr 1
  push_cast
  linear_combination (1 / 2 - (σ : ℂ)) * Complex.I_sq

/-- The mass of `Φ` on `[a, a + 1]`. -/
def unitMass (a : ℝ) : ℝ := ∫ x in a..(a + 1), riemannKernelReal x

theorem unitMass_pos (a : ℝ) : 0 < unitMass a :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuous_riemannKernelReal.intervalIntegrable _ _) (fun x _ => riemannKernelReal_pos x)
    (by linarith)

/-- **The tilted mass sits right of `a`**: `L_0(c) ≥ e^{ca} ∫_a^{a+1} Φ` for `c, a ≥ 0`. -/
theorem heatLaplace_zero_ge {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) :
    Real.exp (c * a) * unitMass a ≤ heatLaplace 0 c := by
  have hint := integrable_heatIntegrand 0 c
  have hnn : ∀ x, 0 ≤ riemannKernelReal x * Real.exp (-0 * x ^ 2) * Real.exp (c * x) := fun x => by
    have := (riemannKernelReal_pos x).le; positivity
  calc Real.exp (c * a) * unitMass a
      = ∫ x in a..(a + 1), Real.exp (c * a) * riemannKernelReal x := by
        rw [unitMass, intervalIntegral.integral_const_mul]
    _ ≤ ∫ x in a..(a + 1), riemannKernelReal x * Real.exp (-0 * x ^ 2) * Real.exp (c * x) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((continuous_riemannKernelReal.const_mul _).intervalIntegrable _ _)
          ((continuous_heatIntegrand 0 c).intervalIntegrable _ _) fun x hx => ?_
        have hΦ := (riemannKernelReal_pos x).le
        have he : Real.exp (c * a) ≤ Real.exp (c * x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.1 hc)
        rw [heatIntegrand_zero]
        nlinarith
    _ ≤ heatLaplace 0 c := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hint (Eventually.of_forall hnn)

/-- **Upper bound for `τ ≥ 0`.** `L_τ(c) ≤ e^{−τM²} L_0(c) + e^{cM} ∫Φ`. -/
theorem heatLaplace_le {τ c M : ℝ} (hτ : 0 ≤ τ) (hc : 0 ≤ c) (hM : 0 ≤ M) :
    heatLaplace τ c ≤
      Real.exp (-τ * M ^ 2) * heatLaplace 0 c + Real.exp (c * M) * ∫ x, riemannKernelReal x := by
  have h0 := integrable_heatIntegrand 0 c
  unfold heatLaplace
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (h0.const_mul _) (integrable_riemannKernelReal'.const_mul _)]
  refine integral_mono (integrable_heatIntegrand τ c)
    ((h0.const_mul _).add (integrable_riemannKernelReal'.const_mul _)) fun x => ?_
  have hΦ := (riemannKernelReal_pos x).le
  simp only [heatIntegrand_zero]
  by_cases hx : M ≤ |x|
  · have h1 : Real.exp (-τ * x ^ 2) ≤ Real.exp (-τ * M ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have : M ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ hM hx 2
      nlinarith
    have h2 : 0 ≤ Real.exp (c * M) * riemannKernelReal x := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hΦ (Real.exp_pos (c * x)).le)
    nlinarith
  · push Not at hx
    have h1 : Real.exp (-τ * x ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have h2 : Real.exp (c * x) ≤ Real.exp (c * M) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self x) hx.le) hc)
    have h3 : 0 ≤ Real.exp (-τ * M ^ 2) * (riemannKernelReal x * Real.exp (c * x)) := by
      positivity
    have h4 : riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x) ≤
        Real.exp (c * M) * riemannKernelReal x := by
      calc riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x)
          ≤ riemannKernelReal x * 1 * Real.exp (c * M) := by gcongr
        _ = _ := by ring
    linarith

/-- **Lower bound for `τ ≤ 0`.** `L_τ(c) ≥ e^{−τM²} (L_0(c) − e^{cM} ∫Φ)`. -/
theorem heatLaplace_ge_of_nonpos {τ c M : ℝ} (hτ : τ ≤ 0) (hc : 0 ≤ c) (hM : 0 ≤ M) :
    Real.exp (-τ * M ^ 2) * (heatLaplace 0 c - Real.exp (c * M) * ∫ x, riemannKernelReal x) ≤
      heatLaplace τ c := by
  have h0 := integrable_heatIntegrand 0 c
  unfold heatLaplace
  rw [← integral_const_mul, ← integral_sub h0 (integrable_riemannKernelReal'.const_mul _),
    ← integral_const_mul]
  refine integral_mono (((h0.sub (integrable_riemannKernelReal'.const_mul _))).const_mul _)
    (integrable_heatIntegrand τ c) fun x => ?_
  have hΦ := (riemannKernelReal_pos x).le
  simp only [heatIntegrand_zero]
  by_cases hx : M ≤ |x|
  · have h1 : Real.exp (-τ * M ^ 2) ≤ Real.exp (-τ * x ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have : M ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ hM hx 2
      nlinarith
    have h2 : 0 ≤ Real.exp (c * M) * riemannKernelReal x := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hΦ (Real.exp_pos (c * x)).le)
    have h4 : 0 ≤ Real.exp (-τ * M ^ 2) * (Real.exp (c * M) * riemannKernelReal x) := by
      positivity
    nlinarith
  · push Not at hx
    have h2 : Real.exp (c * x) ≤ Real.exp (c * M) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self x) hx.le) hc)
    have h3 : riemannKernelReal x * Real.exp (c * x) - Real.exp (c * M) * riemannKernelReal x ≤ 0 := by
      nlinarith
    have h4 : 0 ≤ riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x) := by positivity
    have h5 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-τ * M ^ 2)).le h3
    linarith

/-- The tail constant `C₀ ∫ e^{−|x|} + ∫ Φ`. -/
def tailConst : ℝ := riemannEnvelopeConst * (∫ x, Real.exp (-|x|)) + ∫ x, riemannKernelReal x

theorem one_le_log_two_mul_add_six {c : ℝ} (hc : 0 ≤ c) : 1 ≤ Real.log (2 * c + 6) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- **The envelope beyond `log(2c + 6)`.** `Φ(x) e^{cx} ≤ C₀ e^{−x−c}` for `x ≥ log(2c + 6)`. -/
theorem riemannKernelReal_mul_exp_le {c x : ℝ} (hc : 0 ≤ c) (hx : Real.log (2 * c + 6) ≤ x) :
    riemannKernelReal x * Real.exp (c * x) ≤ riemannEnvelopeConst * Real.exp (-|x|) * Real.exp (-c) := by
  have hB := one_le_log_two_mul_add_six hc
  have hx0 : 0 ≤ x := by linarith
  have hex : 2 * c + 6 ≤ Real.exp x := by
    calc 2 * c + 6 = Real.exp (Real.log (2 * c + 6)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hx1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have he2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have hbig : (2 * c + 6) * (x + 1) ≤ Real.exp (2 * x) := by
    rw [he2]; exact mul_le_mul hex hx1 (by linarith) (Real.exp_pos _).le
  have h3 : 3 ≤ Real.exp (2 * |x|) := by rw [abs_of_nonneg hx0]; nlinarith
  have hΦ := riemannKernelReal_le_envelope h3
  rw [abs_of_nonneg hx0] at hΦ ⊢
  have hC := riemannEnvelopeConst_pos
  unfold kernelEnvelope at hΦ
  have hexp : Real.exp (9 * x / 2) * Real.exp (-π * Real.exp (2 * x)) * Real.exp (c * x) ≤
      Real.exp (-x) * Real.exp (-c) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hπ : 1 ≤ π := by linarith [Real.pi_gt_three]
    have hE : 0 ≤ Real.exp (2 * x) := (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_right hπ hE]
  calc riemannKernelReal x * Real.exp (c * x)
      ≤ riemannEnvelopeConst * (Real.exp (9 * x / 2) * Real.exp (-π * Real.exp (2 * x))) *
          Real.exp (c * x) := mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le
    _ = riemannEnvelopeConst * (Real.exp (9 * x / 2) * Real.exp (-π * Real.exp (2 * x)) *
          Real.exp (c * x)) := by ring
    _ ≤ riemannEnvelopeConst * (Real.exp (-x) * Real.exp (-c)) :=
        mul_le_mul_of_nonneg_left hexp hC.le
    _ = _ := by ring

/-- **Lower bound for `τ ≥ 0`.** `L_τ(c) ≥ e^{−τ log(2c+6)²} (L_0(c) − e^{−c} K)`. -/
theorem heatLaplace_ge {τ c : ℝ} (hτ : 0 ≤ τ) (hc : 0 ≤ c) :
    Real.exp (-τ * Real.log (2 * c + 6) ^ 2) * (heatLaplace 0 c - Real.exp (-c) * tailConst) ≤
      heatLaplace τ c := by
  set B := Real.log (2 * c + 6) with hBdef
  have hB := one_le_log_two_mul_add_six hc
  have h0 := integrable_heatIntegrand 0 c
  have hT : Integrable fun x : ℝ =>
      riemannEnvelopeConst * Real.exp (-|x|) + riemannKernelReal x :=
    (integrable_exp_neg_abs'.const_mul _).add integrable_riemannKernelReal'
  have hTval : ∫ x : ℝ, (riemannEnvelopeConst * Real.exp (-|x|) + riemannKernelReal x) =
      tailConst := by
    rw [integral_add (integrable_exp_neg_abs'.const_mul _) integrable_riemannKernelReal',
      integral_const_mul, tailConst]
  unfold heatLaplace
  rw [← hTval, ← integral_const_mul, ← integral_sub h0 (hT.const_mul _), ← integral_const_mul]
  refine integral_mono ((h0.sub (hT.const_mul _)).const_mul _)
    (integrable_heatIntegrand τ c) fun x => ?_
  have hΦ := (riemannKernelReal_pos x).le
  have hC := riemannEnvelopeConst_pos
  simp only [heatIntegrand_zero]
  have hRHS : 0 ≤ riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x) := by positivity
  have hT0 : 0 ≤ Real.exp (-c) * (riemannEnvelopeConst * Real.exp (-|x|) + riemannKernelReal x) := by
    positivity
  rcases lt_or_ge B x with hxB | hxB
  · -- beyond `B`: the envelope
    have hle := riemannKernelReal_mul_exp_le hc hxB.le
    have hneg : riemannKernelReal x * Real.exp (c * x) -
        Real.exp (-c) * (riemannEnvelopeConst * Real.exp (-|x|) + riemannKernelReal x) ≤ 0 := by
      have : 0 ≤ Real.exp (-c) * riemannKernelReal x := by positivity
      nlinarith
    have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-τ * B ^ 2)).le hneg
    linarith
  · rcases lt_or_ge x (-1) with hx1 | hx1
    · -- left of `−1`
      have he : Real.exp (c * x) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by nlinarith)
      have hneg : riemannKernelReal x * Real.exp (c * x) -
          Real.exp (-c) * (riemannEnvelopeConst * Real.exp (-|x|) + riemannKernelReal x) ≤ 0 := by
        have : 0 ≤ Real.exp (-c) * (riemannEnvelopeConst * Real.exp (-|x|)) := by positivity
        nlinarith
      have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-τ * B ^ 2)).le hneg
      linarith
    · -- on `[−1, B]`: `e^{−τx²} ≥ e^{−τB²}`
      have hxsq : x ^ 2 ≤ B ^ 2 := by nlinarith
      have h1 : Real.exp (-τ * B ^ 2) ≤ Real.exp (-τ * x ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hΦ (Real.exp_pos (c * x)).le)
      have h4 : 0 ≤ Real.exp (-τ * B ^ 2) *
          (Real.exp (-c) * (riemannEnvelopeConst * Real.exp (-|x|) + riemannKernelReal x)) := by
        positivity
      nlinarith

/-! ### The ratio `ξ_τ/ξ` on the real axis -/

/-- **For `τ > 0` the ratio tends to zero.** -/
theorem tendsto_ratio_zero {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun c => heatLaplace τ c / heatLaplace 0 c) atTop (𝓝 0) := by
  have hpos : ∀ c, 0 ≤ c → 0 < heatLaplace 0 c := fun c hc =>
    lt_of_lt_of_le (by have := unitMass_pos 0; positivity) (heatLaplace_zero_ge hc le_rfl)
  set I := ∫ x, riemannKernelReal x with hI
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun c => lt_of_lt_of_le ha
    (div_nonneg (heatLaplace_nonneg _ _) (heatLaplace_nonneg _ _)), fun ε hε => ?_⟩
  -- choose `M` with `e^{−τM²} < ε/2`
  obtain ⟨M, hM0, hMε⟩ : ∃ M : ℝ, 0 ≤ M ∧ Real.exp (-τ * M ^ 2) < ε / 2 := by
    have ht : Tendsto (fun M : ℝ => Real.exp (-τ * M ^ 2)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have h2 : Tendsto (fun M : ℝ => M ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
      exact (h2.const_mul_atTop hτ).neg_atTop_atBot.congr fun M => by ring
    obtain ⟨M, hM⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).and
      (eventually_ge_atTop 0) |>.exists
    exact ⟨M, hM.2, hM.1⟩
  set m := unitMass (M + 1) with hm
  have hm0 : 0 < m := unitMass_pos _
  have hI0 : 0 ≤ I := integral_nonneg fun x => (riemannKernelReal_pos x).le
  have hsmall : ∀ᶠ c in atTop, Real.exp (-c) * I / m < ε / 2 := by
    have ht : Tendsto (fun c : ℝ => Real.exp (-c) * I / m) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const (I / m)
      simpa [mul_div_assoc] using this
    exact ht.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with c hc hc0
  have hup := heatLaplace_le hτ.le hc0 hM0
  have hlow := heatLaplace_zero_ge hc0 (by linarith : (0 : ℝ) ≤ M + 1)
  rw [← hm] at hlow
  have hL0 := hpos c hc0
  rw [div_lt_iff₀ hL0]
  have hexp : Real.exp (c * M) * I ≤ Real.exp (-c) * I / m * heatLaplace 0 c := by
    have he : Real.exp (c * M) = Real.exp (-c) * Real.exp (c * (M + 1)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have : Real.exp (-c) * I / m * (Real.exp (c * (M + 1)) * m) =
        Real.exp (-c) * Real.exp (c * (M + 1)) * I := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ Real.exp (-c) * I / m)
    linarith
  have h1 := mul_lt_mul_of_pos_right hMε hL0
  nlinarith

/-- **For `τ > 0` the ratio is at least `½ e^{−τ log(2c+6)²}` eventually.** -/
theorem eventually_ratio_ge {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᶠ c in atTop, Real.exp (-τ * Real.log (2 * c + 6) ^ 2) / 2 ≤
      heatLaplace τ c / heatLaplace 0 c := by
  set κ := unitMass 0 with hκ
  have hκ0 : 0 < κ := unitMass_pos 0
  have hsmall : ∀ᶠ c in atTop, Real.exp (-c) * tailConst ≤ κ / 2 := by
    have ht : Tendsto (fun c : ℝ => Real.exp (-c) * tailConst) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const tailConst
    exact (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < κ / 2))).mono fun c h => h.le
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with c hc hc0
  have hlow := heatLaplace_zero_ge hc0 (le_refl 0)
  rw [mul_zero, Real.exp_zero, one_mul, ← hκ] at hlow
  have hL0 : 0 < heatLaplace 0 c := lt_of_lt_of_le hκ0 hlow
  have hge := heatLaplace_ge hτ hc0
  rw [le_div_iff₀ hL0]
  have he := Real.exp_pos (-τ * Real.log (2 * c + 6) ^ 2)
  nlinarith

/-- **For `τ < 0` the ratio tends to infinity.** -/
theorem tendsto_ratio_atTop {τ : ℝ} (hτ : τ < 0) :
    Tendsto (fun c => heatLaplace τ c / heatLaplace 0 c) atTop atTop := by
  set I := ∫ x, riemannKernelReal x with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => (riemannKernelReal_pos x).le
  rw [tendsto_atTop]
  intro b
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ 2 * b ≤ Real.exp (-τ * M ^ 2) := by
    have ht : Tendsto (fun M : ℝ => Real.exp (-τ * M ^ 2)) atTop atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by linarith)
    obtain ⟨M, hM⟩ := ((tendsto_atTop.mp ht) (2 * b)).and (eventually_ge_atTop 0) |>.exists
    exact ⟨M, hM.2, hM.1⟩
  set m := unitMass (M + 1) with hm
  have hm0 : 0 < m := unitMass_pos _
  have hsmall : ∀ᶠ c in atTop, Real.exp (-c) * I / m ≤ 1 / 2 := by
    have ht : Tendsto (fun c : ℝ => Real.exp (-c) * I / m) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const (I / m)
      simpa [mul_div_assoc] using this
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun c h => h.le
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with c hc hc0
  have hlow := heatLaplace_ge_of_nonpos hτ.le hc0 hM0
  have hm' := heatLaplace_zero_ge hc0 (by linarith : (0 : ℝ) ≤ M + 1)
  rw [← hm] at hm'
  have hL0 : 0 < heatLaplace 0 c :=
    lt_of_lt_of_le (by positivity) hm'
  have hexp : Real.exp (c * M) * I ≤ heatLaplace 0 c / 2 := by
    have he : Real.exp (c * M) = Real.exp (-c) * Real.exp (c * (M + 1)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have h1 := mul_le_mul_of_nonneg_left hm' (by positivity : 0 ≤ Real.exp (-c) * I / m)
    have h2 : Real.exp (-c) * I / m * (Real.exp (c * (M + 1)) * m) =
        Real.exp (-c) * Real.exp (c * (M + 1)) * I := by field_simp
    have h3 := mul_le_mul_of_nonneg_right hc hL0.le
    nlinarith
  rw [le_div_iff₀ hL0]
  have hE := Real.exp_pos (-τ * M ^ 2)
  nlinarith

/-! ### Dirichlet series on the real axis -/

/-- **An absolutely convergent Dirichlet series tends to its first coefficient**, at rate
`2^{σ₁−σ}`: `|D(σ) − a₁| ≤ 2^{σ₁−σ} Σ_n |a_n| n^{−σ₁}`. -/
theorem norm_LSeries_sub_le {a : ℕ → ℂ} {σ₁ σ : ℝ} (ha : LSeriesSummable a σ₁) (hσ : σ₁ ≤ σ) :
    ‖LSeries a σ - a 1‖ ≤ (2 : ℝ) ^ (σ₁ - σ) * ∑' n, ‖LSeries.term a σ₁ n‖ := by
  have hs : LSeriesSummable a σ := ha.of_re_le_re (by simpa using hσ)
  have hn1 : Summable fun n => ‖LSeries.term a σ₁ n‖ := summable_norm_iff.mpr ha
  set e : ℕ → ℂ := fun n => if n = 1 then a 1 else 0 with he
  have hes : HasSum e (a 1) := by simpa [he] using hasSum_ite_eq 1 (a 1)
  have hdiff : HasSum (fun n => LSeries.term a σ n - e n) (LSeries a σ - a 1) :=
    hs.hasSum.sub hes
  have hbound : ∀ n, ‖LSeries.term a σ n - e n‖ ≤
      (2 : ℝ) ^ (σ₁ - σ) * ‖LSeries.term a σ₁ n‖ := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [he, LSeries.term]
      · simp [he, LSeries.term]
    · have hn0 : n ≠ 0 := by omega
      have hn1' : n ≠ 1 := by omega
      simp only [he, if_neg hn1', sub_zero]
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0]
      simp only [Complex.ofReal_re]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have key : (n : ℝ) ^ (σ₁ - σ) ≤ (2 : ℝ) ^ (σ₁ - σ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2n (by linarith)
      have hsplit : (n : ℝ) ^ σ = (n : ℝ) ^ σ₁ * ((n : ℝ) ^ (σ₁ - σ))⁻¹ := by
        rw [← Real.rpow_neg hnpos.le, ← Real.rpow_add hnpos]; ring_nf
      have hp1 : 0 < (n : ℝ) ^ σ₁ := Real.rpow_pos_of_pos hnpos _
      have hp2 : 0 < (n : ℝ) ^ (σ₁ - σ) := Real.rpow_pos_of_pos hnpos _
      rw [hsplit]
      calc ‖a n‖ / ((n : ℝ) ^ σ₁ * ((n : ℝ) ^ (σ₁ - σ))⁻¹)
          = (n : ℝ) ^ (σ₁ - σ) * (‖a n‖ / (n : ℝ) ^ σ₁) := by field_simp
        _ ≤ (2 : ℝ) ^ (σ₁ - σ) * (‖a n‖ / (n : ℝ) ^ σ₁) :=
            mul_le_mul_of_nonneg_right key (by positivity)
  have hsumN : Summable fun n => ‖LSeries.term a σ n - e n‖ :=
    (hn1.mul_left _).of_nonneg_of_le (fun n => norm_nonneg _) hbound
  rw [← hdiff.tsum_eq]
  refine (norm_tsum_le_tsum_norm hsumN).trans ?_
  rw [← tsum_mul_left]
  exact hasSum_le hbound hsumN.hasSum (hn1.mul_left _).hasSum

theorem rpow_two_eq_exp (x : ℝ) : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

theorem tendsto_two_rpow_sub (σ₁ : ℝ) :
    Tendsto (fun σ : ℝ => (2 : ℝ) ^ (σ₁ - σ)) atTop (𝓝 0) := by
  simp_rw [rpow_two_eq_exp]
  refine Real.tendsto_exp_atBot.comp ?_
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (tendsto_atBot_add_const_left atTop σ₁ tendsto_neg_atTop_atBot).atBot_mul_const hlog
  exact h.congr fun σ => by ring

/-- `|ζ(σ)| ≥ 1/2` for large real `σ`. -/
theorem eventually_half_le_norm_riemannZeta :
    ∀ᶠ σ : ℝ in atTop, 1 / 2 ≤ ‖riemannZeta σ‖ ∧ ‖riemannZeta σ‖ ≤ 3 / 2 := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) ((2 : ℝ) : ℂ) :=
    LSeriesSummable_one_iff.mpr (by simp; norm_num)
  set S := ∑' n, ‖LSeries.term (1 : ℕ → ℂ) ((2 : ℝ) : ℂ) n‖ with hS
  have ht : Tendsto (fun σ : ℝ => (2 : ℝ) ^ ((2 : ℝ) - σ) * S) atTop (𝓝 0) := by
    simpa using (tendsto_two_rpow_sub 2).mul_const S
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (2 : ℝ)] with σ hσ hσ2
  have hb := norm_LSeries_sub_le h1 hσ2
  rw [LSeries_one_eq_riemannZeta (by simp; linarith), Pi.one_apply] at hb
  have hb' : ‖riemannZeta σ - 1‖ < 1 / 2 := lt_of_le_of_lt hb hσ
  have h1n : ‖(1 : ℂ)‖ = 1 := norm_one
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (riemannZeta σ)
    rw [norm_sub_rev] at this
    linarith
  · have := norm_sub_norm_le (riemannZeta σ) 1
    linarith

/-! ### The selector -/

/-- On the real axis, a Dirichlet representation of `ξ_τ` reads `|D(σ)| = R_τ(σ − ½) |ζ(σ)|`. -/
theorem norm_LSeries_eq_ratio {τ : ℝ} {a : ℕ → ℂ} {σ : ℝ} (hσ : 1 < σ)
    (h : riemannHeat (-τ) (((1 / 2 - σ : ℝ) : ℂ) * I) =
      (σ : ℂ) * (σ - 1) / 2 * (Complex.Gammaℝ σ * LSeries a σ)) :
    ‖LSeries a σ‖ =
      heatLaplace τ (σ - 1 / 2) / heatLaplace 0 (σ - 1 / 2) * ‖riemannZeta σ‖ := by
  have hre : 1 < (σ : ℂ).re := by simpa using hσ
  have hxi := xi_eq_mul_Gammaℝ_zeta hre
  rw [xi_eq_heatLaplace] at hxi
  rw [riemannHeat_neg_eq_heatLaplace] at h
  set P : ℂ := (σ : ℂ) * (σ - 1) / 2 * Complex.Gammaℝ σ with hP
  have hΓ : Complex.Gammaℝ σ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hP0 : P ≠ 0 := by
    have h1 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
    have h2 : (σ : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (show σ ≠ 1 by linarith)
    rw [hP]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero h1 h2) two_ne_zero) hΓ
  have hτ' : (heatLaplace τ (σ - 1 / 2) : ℂ) = P * LSeries a σ := by rw [h, hP]; ring
  have h0' : (heatLaplace 0 (σ - 1 / 2) : ℂ) = P * riemannZeta σ := by rw [hxi, hP]; ring
  have hn1 := congrArg norm hτ'
  have hn0 := congrArg norm h0'
  rw [Complex.norm_real, Real.norm_of_nonneg (heatLaplace_nonneg _ _), norm_mul] at hn1 hn0
  have hPn : 0 < ‖P‖ := norm_pos_iff.mpr hP0
  have hL0 : 0 < heatLaplace 0 (σ - 1 / 2) := by
    rw [hn0]
    exact mul_pos hPn (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hre))
  rw [hn1, hn0]
  field_simp

/-- **No deformed kernel has a Dirichlet series.** For `τ ≠ 0` there is no absolutely convergent
Dirichlet series `D` with `ξ_τ(σ) = ½σ(σ−1)Γ_ℝ(σ) D(σ)` on a real half-line. -/
theorem not_exists_dirichlet_of_ne_zero {τ : ℝ} (hτ : τ ≠ 0) :
    ¬ ∃ (a : ℕ → ℂ) (σ₁ : ℝ), LSeriesSummable a σ₁ ∧ ∀ σ : ℝ, σ₁ < σ →
      riemannHeat (-τ) (((1 / 2 - σ : ℝ) : ℂ) * I) =
        (σ : ℂ) * (σ - 1) / 2 * (Complex.Gammaℝ σ * LSeries a σ) := by
  rintro ⟨a, σ₁, ha, hrep⟩
  set S := ∑' n, ‖LSeries.term a σ₁ n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have hshift : Tendsto (fun σ : ℝ => σ - 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  -- the representation on a half-line
  have hD : ∀ᶠ σ : ℝ in atTop, ‖LSeries a σ‖ =
      heatLaplace τ (σ - 1 / 2) / heatLaplace 0 (σ - 1 / 2) * ‖riemannZeta σ‖ := by
    filter_upwards [eventually_gt_atTop (max σ₁ 1)] with σ hσ
    exact norm_LSeries_eq_ratio (lt_of_le_of_lt (le_max_right _ _) hσ)
      (hrep σ (lt_of_le_of_lt (le_max_left _ _) hσ))
  have hdir : ∀ᶠ σ : ℝ in atTop, ‖LSeries a σ - a 1‖ ≤ (2 : ℝ) ^ (σ₁ - σ) * S := by
    filter_upwards [eventually_ge_atTop σ₁] with σ hσ
    exact norm_LSeries_sub_le ha hσ
  have hζ := eventually_half_le_norm_riemannZeta
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · -- `τ < 0`: a bounded Dirichlet series against an unbounded ratio
    have hR := (tendsto_ratio_atTop hneg).comp hshift
    have hbig := (tendsto_atTop.mp hR) (2 * (‖a 1‖ + S) + 1)
    obtain ⟨σ, hσD, hσdir, hσζ, hσbig, hσ1⟩ :=
      (hD.and (hdir.and (hζ.and (hbig.and (eventually_ge_atTop σ₁))))).exists
    have h2 : (2 : ℝ) ^ (σ₁ - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hup : ‖LSeries a σ‖ ≤ ‖a 1‖ + S := by
      have := norm_le_insert' (LSeries a σ) (a 1)
      have h3 : (2 : ℝ) ^ (σ₁ - σ) * S ≤ S := by nlinarith
      linarith
    simp only [Function.comp_apply] at hσbig
    have hR0 : 0 ≤ heatLaplace τ (σ - 1 / 2) / heatLaplace 0 (σ - 1 / 2) :=
      div_nonneg (heatLaplace_nonneg _ _) (heatLaplace_nonneg _ _)
    rw [hσD] at hup
    nlinarith [hσζ.1]
  · -- `τ > 0`: first the leading coefficient vanishes, then exponential decay meets the floor
    have hR0 := (tendsto_ratio_zero hpos).comp hshift
    have ha1 : a 1 = 0 := by
      have hlim : Tendsto (fun σ : ℝ => (3 / 2) * (heatLaplace τ (σ - 1 / 2) /
          heatLaplace 0 (σ - 1 / 2)) + (2 : ℝ) ^ (σ₁ - σ) * S) atTop (𝓝 0) := by
        simpa using (hR0.const_mul (3 / 2)).add ((tendsto_two_rpow_sub σ₁).mul_const S)
      have hle : ∀ᶠ σ : ℝ in atTop, ‖a 1‖ ≤ (3 / 2) * (heatLaplace τ (σ - 1 / 2) /
          heatLaplace 0 (σ - 1 / 2)) + (2 : ℝ) ^ (σ₁ - σ) * S := by
        filter_upwards [hD, hdir, hζ] with σ hσD hσdir hσζ
        have hR : 0 ≤ heatLaplace τ (σ - 1 / 2) / heatLaplace 0 (σ - 1 / 2) :=
          div_nonneg (heatLaplace_nonneg _ _) (heatLaplace_nonneg _ _)
        have h1 : ‖a 1‖ ≤ ‖LSeries a σ‖ + ‖LSeries a σ - a 1‖ := by
          have := norm_sub_norm_le (a 1) (LSeries a σ)
          rw [norm_sub_rev] at this
          linarith
        rw [hσD] at h1
        nlinarith [hσζ.2]
      have := le_of_tendsto hlim hle
      exact norm_le_zero_iff.mp this
    -- the floor `e^{−τ log(2σ+5)²}/4` against `2^{σ₁−σ} S`
    have hfloor := hshift.eventually (eventually_ratio_ge hpos.le)
    have hlog : ∀ᶠ σ : ℝ in atTop, τ * Real.log (2 * σ + 5) ^ 2 ≤ σ * Real.log 2 / 2 := by
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have ht := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-5 / 2) 2 (by norm_num)).comp
        (tendsto_atTop_add_const_right _ 5 (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
      have ht' : Tendsto (fun σ : ℝ => Real.log (2 * σ + 5) ^ 2 / σ) atTop (𝓝 0) :=
        ht.congr' (Eventually.of_forall fun σ => by simp only [Function.comp_apply, id]; ring_nf)
      filter_upwards [ht'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < Real.log 2 / (2 * τ))),
        eventually_gt_atTop (0 : ℝ)] with σ hσ hσ0
      rw [div_lt_iff₀ hσ0] at hσ
      have : τ * (Real.log 2 / (2 * τ) * σ) = σ * Real.log 2 / 2 := by field_simp
      nlinarith
    have hgrow : Tendsto (fun σ : ℝ => Real.exp (σ * Real.log 2 / 2)) atTop atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      have hl2 : 0 < Real.log 2 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
      exact (tendsto_id.atTop_mul_const hl2).congr fun σ => by simp only [id]; ring
    have hbig := (tendsto_atTop.mp hgrow) (8 * Real.exp (σ₁ * Real.log 2) * S + 1)
    obtain ⟨σ, hσD, hσdir, hσζ, hσfl, hσlog, hσbig⟩ :=
      (hD.and (hdir.and (hζ.and (hfloor.and (hlog.and hbig))))).exists
    rw [ha1, sub_zero] at hσdir
    rw [hσD] at hσdir
    have hratio := hσfl
    have hc : 2 * (σ - 1 / 2) + 6 = 2 * σ + 5 := by ring
    rw [hc] at hratio
    -- `e^{−τ log²}/2 ≤ R`, `R/2 ≤ |D| ≤ 2^{σ₁−σ} S`
    have hR0 : 0 ≤ heatLaplace τ (σ - 1 / 2) / heatLaplace 0 (σ - 1 / 2) :=
      div_nonneg (heatLaplace_nonneg _ _) (heatLaplace_nonneg _ _)
    have h1 : Real.exp (-τ * Real.log (2 * σ + 5) ^ 2) / 4 ≤ (2 : ℝ) ^ (σ₁ - σ) * S := by
      nlinarith [hσζ.1]
    have h2 : Real.exp (-(σ * Real.log 2 / 2)) ≤ Real.exp (-τ * Real.log (2 * σ + 5) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [rpow_two_eq_exp] at h1
    have h3 : Real.exp ((σ₁ - σ) * Real.log 2) =
        Real.exp (σ₁ * Real.log 2) * Real.exp (-(σ * Real.log 2 / 2)) *
          Real.exp (-(σ * Real.log 2 / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h4 : Real.exp (σ * Real.log 2 / 2) * Real.exp (-(σ * Real.log 2 / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    set u := Real.exp (-(σ * Real.log 2 / 2)) with hu
    have hu0 : 0 < u := Real.exp_pos _
    have hE0 : 0 < Real.exp (σ₁ * Real.log 2) := Real.exp_pos _
    rw [h3] at h1
    -- `u/4 ≤ e^{σ₁ log 2} u² S`, so `1 ≤ 4 e^{σ₁ log 2} S u`, i.e. `e^{σ log 2/2} ≤ 4 e^{σ₁ log 2} S`
    have h5 : u / 4 ≤ Real.exp (σ₁ * Real.log 2) * u * u * S := by linarith
    have h6 : 1 ≤ 4 * Real.exp (σ₁ * Real.log 2) * S * u := by
      have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp h5
      nlinarith
    have h7 : Real.exp (σ * Real.log 2 / 2) ≤ 4 * Real.exp (σ₁ * Real.log 2) * S := by
      have := mul_le_mul_of_nonneg_left h6 (Real.exp_pos (σ * Real.log 2 / 2)).le
      nlinarith
    linarith

/-- **The time-zero selector.** `ξ_τ` is `½s(s−1)Γ_ℝ(s)` times an absolutely convergent Dirichlet
series on a real half-line iff `τ = 0`. -/
theorem exists_dirichlet_iff (τ : ℝ) :
    (∃ (a : ℕ → ℂ) (σ₁ : ℝ), LSeriesSummable a σ₁ ∧ ∀ σ : ℝ, σ₁ < σ →
      riemannHeat (-τ) (((1 / 2 - σ : ℝ) : ℂ) * I) =
        (σ : ℂ) * (σ - 1) / 2 * (Complex.Gammaℝ σ * LSeries a σ)) ↔ τ = 0 := by
  refine ⟨fun h => by_contra fun hτ => not_exists_dirichlet_of_ne_zero hτ h, ?_⟩
  rintro rfl
  refine ⟨1, 2, LSeriesSummable_one_iff.mpr (by simp; norm_num), fun σ hσ => ?_⟩
  have hre : 1 < (σ : ℂ).re := by simp; linarith
  rw [riemannHeat_neg_eq_heatLaplace, ← xi_eq_heatLaplace, xi_eq_mul_Gammaℝ_zeta hre,
    LSeries_one_eq_riemannZeta hre]

end GaloisForLFunctions.ZeroConfigurationGeometry
