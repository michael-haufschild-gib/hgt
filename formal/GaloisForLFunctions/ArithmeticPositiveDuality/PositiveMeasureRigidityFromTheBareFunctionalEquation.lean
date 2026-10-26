import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureHamburgerRigidity
import GaloisForLFunctions.HTGeometry.HamburgerThetaDefect

/-!
# Positive-measure rigidity from the bare functional equation

`measure_eq_of_completed_functional_equation` identifies a nonnegative measure `ν` on `[1, ∞)` as a
multiple of the integer counting measure when `Γ_ℝ(s) D_ν(s)` and `Γ_ℝ(1 - s) D_ν(1 - s)` share a
continuation `E` across `-1/2 ≤ Re s ≤ 3/2`, up to the polar part `α Γ_ℝ(s) + β Γ_ℝ(s - 1)`, with the
decay premise `‖E(s)‖ ≤ C/(1 + (Im s)²)` on the strip.

That premise is a consequence of the functional equation itself. On the two boundary lines `E` is
`Γ_ℝ` times an absolutely convergent integral minus Gamma factors, so it decays like `1/(1 + t²)`.
Phragmén–Lindelöf, applied to `E` and then to `E(s)(s + 2)²`, carries this decay into the strip
from any finite-order bound `‖E(s)‖ ≤ C₀ e^{‖s‖^ρ}`.

**Theorem** (`measure_eq_of_completed_functional_equation_of_finiteOrder`). Hamburger's rigidity
for positive measures holds with the classical hypotheses: absolute convergence on `Re s = 3/2`,
the completed functional equation, and finite order of the completion in the strip.
-/

open Complex MeasureTheory Filter Topology Set Asymptotics

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

/-! ## 1. Growth below the Phragmén–Lindelöf threshold -/

/-- Finite order on the closed strip `1 − N ≤ Re s ≤ N` is below the Phragmén–Lindelöf threshold
`π/(2N − 1)`. -/
theorem isBigO_strip_of_finiteOrder_on {E : ℂ → ℂ} {ρ C₀ N : ℝ} (hN : 1 ≤ N)
    (hfin : ∀ s ∈ verticalStrip (1 - N) N, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ)) :
    ∃ c < Real.pi / (N - (1 - N)), ∃ B,
      E =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  have hw : 0 < N - (1 - N) := by linarith
  set c : ℝ := Real.pi / (2 * (N - (1 - N))) with hc
  have hc0 : 0 < c := by positivity
  set n : ℕ := ⌈ρ⌉₊ with hn
  set B : ℝ := (2 * N / c) ^ n * n.factorial * Real.exp (N * c) with hB
  refine ⟨c, ?_, B, ?_⟩
  · rw [hc, div_lt_div_iff₀ (by positivity) hw]
    nlinarith [Real.pi_pos]
  refine IsBigO.of_bound C₀ ?_
  have him : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N),
      1 ≤ |z.im| := by
    refine Eventually.filter_mono inf_le_left ?_
    exact (eventually_ge_atTop (1 : ℝ)).comap _
  have hre : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N),
      z.re ∈ Ioo (1 - N) N :=
    Eventually.filter_mono inf_le_right (eventually_principal.mpr fun z hz => hz)
  filter_upwards [him, hre] with z hz hzre
  set t := |z.im| with ht
  have hz1 : 1 ≤ ‖z‖ := hz.trans (Complex.abs_im_le_norm z)
  have hz2 : ‖z‖ ≤ N + t := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ N + t := by
          have : |z.re| ≤ N := abs_le.mpr ⟨by linarith [hzre.1], hzre.2.le⟩
          linarith
  have hpow : ‖z‖ ^ ρ ≤ ‖z‖ ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (Nat.le_ceil ρ)
  have hpow2 : ‖z‖ ^ n ≤ B * Real.exp (c * t) := by
    have h := Real.pow_div_factorial_le_exp (c / (2 * N) * (N + t)) (by positivity) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hf] at h
    have e1 : (N + t) ^ n = (2 * N / c) ^ n * (c / (2 * N) * (N + t)) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 : Real.exp (c / (2 * N) * (N + t)) ≤ Real.exp (N * c) * Real.exp (c * t) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hN0 : 0 < N := by linarith
      have e : c / (2 * N) * (N + t) = c / 2 + c * t / (2 * N) := by field_simp
      have ht0 : 0 ≤ t := abs_nonneg _
      have h1 : c / 2 ≤ N * c := by nlinarith
      have h2 : c * t / (2 * N) ≤ c * t := div_le_self (by positivity) (by linarith)
      linarith
    calc ‖z‖ ^ n ≤ (N + t) ^ n := pow_le_pow_left₀ (norm_nonneg _) hz2 n
      _ = (2 * N / c) ^ n * (c / (2 * N) * (N + t)) ^ n := e1
      _ ≤ (2 * N / c) ^ n * (Real.exp (c / (2 * N) * (N + t)) * n.factorial) := by gcongr
      _ ≤ (2 * N / c) ^ n * ((Real.exp (N * c) * Real.exp (c * t)) * n.factorial) := by gcongr
      _ = B * Real.exp (c * t) := by rw [hB]; ring
  have hzs : z ∈ verticalStrip (1 - N) N := ⟨hzre.1.le, hzre.2.le⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hfin z hzs).trans ?_
  have hC0 : 0 ≤ C₀ := by
    have := (norm_nonneg (E z)).trans (hfin z hzs)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  gcongr
  exact hpow.trans hpow2

/-! ## 2. Decay in the strip from decay on its edges -/

theorem diffContOnCl_of_differentiableOn_verticalStrip {f : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) :
    DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo a b) := by
  refine DifferentiableOn.diffContOnCl ?_
  have hcl : closure (Complex.re ⁻¹' Ioo a b) = verticalStrip a b := by
    rw [Complex.closure_preimage_re, closure_Ioo hab.ne]
    rfl
  rwa [hcl]

/-- **Phragmén–Lindelöf decay.** If `f` is differentiable on the closed strip
`-1/2 ≤ Re s ≤ 3/2`, of finite order there, and `‖f(s)‖ ≤ C/(1 + (Im s)²)` on both edges, then
`‖f(s)‖ ≤ 13 C/(1 + (Im s)²)` on the whole strip. -/
theorem norm_le_of_edges_of_finiteOrder {f : ℂ → ℂ} {C C₀ ρ : ℝ}
    (hf : DifferentiableOn ℂ f (verticalStrip (-1 / 2) (3 / 2)))
    (hfin : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖f s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → ‖f s‖ ≤ C / (1 + s.im ^ 2))
    (hL : ∀ s : ℂ, s.re = -1 / 2 → ‖f s‖ ≤ C / (1 + s.im ^ 2)) :
    ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖f s‖ ≤ 13 * C / (1 + s.im ^ 2) := by
  have hab : (-1 / 2 : ℝ) < 3 / 2 := by norm_num
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hR ((3 / 2 : ℝ) : ℂ) (by simp))
    exact (div_nonneg_iff.mp h).elim (fun h => h.1) fun h => by
      have : (0 : ℝ) < 1 + (((3 / 2 : ℝ) : ℂ)).im ^ 2 := by positivity
      linarith [h.2]
  have hstrip : (1 - (3 / 2 : ℝ)) = -1 / 2 := by norm_num
  -- Step 1: `f` is bounded by `C` on the strip.
  have hbdd : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖f s‖ ≤ C := by
    intro s hs
    have hfin' : ∀ s ∈ verticalStrip (1 - (3 / 2 : ℝ)) (3 / 2),
        ‖f s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ) := by rw [hstrip]; exact hfin
    obtain ⟨c, hc, B, hO⟩ := isBigO_strip_of_finiteOrder_on (N := 3 / 2) (by norm_num) hfin'
    rw [hstrip] at hc hO
    refine PhragmenLindelof.vertical_strip (diffContOnCl_of_differentiableOn_verticalStrip hab hf)
      ⟨c, hc, B, hO⟩ (fun z hz => ?_) (fun z hz => ?_) hs.1 hs.2
    · exact (hL z hz).trans (div_le_self hC (by nlinarith [sq_nonneg z.im]))
    · exact (hR z hz).trans (div_le_self hC (by nlinarith [sq_nonneg z.im]))
  -- Step 2: `f(s)(s + 2)²` is bounded by `13 C` on the strip.
  have hsq : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      1 + s.im ^ 2 ≤ ‖s + 2‖ ^ 2 ∧ ‖s + 2‖ ^ 2 ≤ 13 * (1 + s.im ^ 2) := by
    intro s h1 h2
    have hn : ‖s + 2‖ ^ 2 = (s.re + 2) ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    rw [hn]
    constructor <;> nlinarith [sq_nonneg s.im]
  set F : ℂ → ℂ := fun s => f s * (s + 2) ^ 2 with hF
  have hFd : DifferentiableOn ℂ F (verticalStrip (-1 / 2) (3 / 2)) :=
    hf.mul ((differentiable_id.add_const 2).pow 2).differentiableOn
  have hFn : ∀ s, ‖F s‖ = ‖f s‖ * ‖s + 2‖ ^ 2 := fun s => by
    simp only [hF, norm_mul, norm_pow]
  have hFedge : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖f s‖ ≤ C / (1 + s.im ^ 2) →
      ‖F s‖ ≤ 13 * C := by
    intro s h1 h2 hfs
    obtain ⟨-, hup⟩ := hsq s h1 h2
    rw [hFn]
    calc ‖f s‖ * ‖s + 2‖ ^ 2 ≤ C / (1 + s.im ^ 2) * (13 * (1 + s.im ^ 2)) :=
          mul_le_mul hfs hup (by positivity) (by positivity)
      _ = 13 * C := by field_simp
  have hFbdd : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖F s‖ ≤ 13 * C := by
    intro s hs
    have hgrowth : F =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 / 2) (3 / 2))]
        fun z => Real.exp (2 * Real.exp (1 * |z.im|)) := by
      refine IsBigO.of_bound (13 * C) ?_
      have hre : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓
          𝓟 (Complex.re ⁻¹' Ioo (-1 / 2) (3 / 2)), z.re ∈ Ioo (-1 / 2 : ℝ) (3 / 2) :=
        Eventually.filter_mono inf_le_right (eventually_principal.mpr fun z hz => hz)
      filter_upwards [hre] with z hz
      have hzs : z ∈ verticalStrip (-1 / 2) (3 / 2) := ⟨hz.1.le, hz.2.le⟩
      obtain ⟨-, hup⟩ := hsq z hz.1.le hz.2.le
      have h1 : 1 + z.im ^ 2 ≤ Real.exp (2 * Real.exp (1 * |z.im|)) := by
        have ha := Real.add_one_le_exp |z.im|
        have hb : |z.im| ≤ Real.exp (1 * |z.im|) := by
          rw [one_mul]; linarith [Real.add_one_le_exp |z.im|]
        have hc : (1 + |z.im|) ^ 2 ≤ Real.exp |z.im| ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        have hd : Real.exp |z.im| ^ 2 = Real.exp (2 * |z.im|) := by
          rw [sq, ← Real.exp_add]; ring_nf
        have he : Real.exp (2 * |z.im|) ≤ Real.exp (2 * Real.exp (1 * |z.im|)) :=
          Real.exp_le_exp.mpr (by linarith)
        have hsq' : 1 + z.im ^ 2 ≤ (1 + |z.im|) ^ 2 := by
          nlinarith [abs_nonneg z.im, sq_abs z.im]
        linarith
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hFn]
      calc ‖f z‖ * ‖z + 2‖ ^ 2 ≤ C * (13 * (1 + z.im ^ 2)) :=
            mul_le_mul (hbdd z hzs) hup (by positivity) hC
        _ = 13 * C * (1 + z.im ^ 2) := by ring
        _ ≤ 13 * C * Real.exp (2 * Real.exp (1 * |z.im|)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hc1 : (1 : ℝ) < Real.pi / (3 / 2 - (-1 / 2)) := by
      rw [lt_div_iff₀ (by norm_num)]; linarith [Real.pi_gt_three]
    refine PhragmenLindelof.vertical_strip (diffContOnCl_of_differentiableOn_verticalStrip hab hFd)
      ⟨1, hc1, 2, hgrowth⟩ (fun z hz => ?_) (fun z hz => ?_) hs.1 hs.2
    · exact hFedge z (by rw [hz]) (by rw [hz]; norm_num) (hL z hz)
    · exact hFedge z (by rw [hz]; norm_num) (by rw [hz]) (hR z hz)
  -- Step 3: divide by `‖s + 2‖² ≥ 1 + (Im s)²`.
  intro s hs
  obtain ⟨hlow, -⟩ := hsq s hs.1 hs.2
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  have hF := hFbdd s hs
  rw [hFn] at hF
  rw [le_div_iff₀ hpos]
  calc ‖f s‖ * (1 + s.im ^ 2) ≤ ‖f s‖ * ‖s + 2‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ ≤ 13 * C := hF

/-! ## 3. The edges -/

/-- `‖D_ν(s)‖ ≤ ∫ u^{-3/2} dν` on `Re s = 3/2`. -/
theorem norm_measureDirichlet_le {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0)
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖measureDirichlet ν s‖ ≤ ∫ u : ℝ, u ^ (-(3 / 2 : ℝ)) ∂ν := by
  unfold measureDirichlet
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.neg_re, hs]

/-- `Γ_ℝ` decays like `1/(1 + (Im s)²)` on every line `Re s = a` avoiding its poles. -/
theorem exists_decay_Gammaℝ_of_re {a : ℝ} (ha : ∀ k : ℕ, a ≠ -(2 * k)) :
    ∃ C : ℝ, ∀ s : ℂ, s.re = a → ‖Complex.Gammaℝ s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C, hC⟩ := exists_decay_Gammaℝ_vertical_line ha
  refine ⟨C, fun s hs => ?_⟩
  have h := hC s.im
  rwa [show ((a : ℂ) + (s.im : ℂ) * I) = s by
    rw [← hs]; exact Complex.re_add_im s] at h

/-- The four edge abscissae avoid the poles `0, -2, -4, …` of `Γ_ℝ`. -/
private theorem ne_neg_two_mul_of_frac {a : ℝ} (ha : a = 3 / 2 ∨ a = 1 / 2 ∨ a = -1 / 2 ∨
    a = -3 / 2) (k : ℕ) : a ≠ -(2 * k) := by
  intro h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases ha with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · -- `2k = 1/2` has no natural solution
    have h1 : (4 : ℝ) * k = 1 := by linarith
    have h2 : (4 * k : ℕ) = 1 := by exact_mod_cast h1
    omega
  · have h1 : (4 : ℝ) * k = 3 := by linarith
    have h2 : (4 * k : ℕ) = 3 := by exact_mod_cast h1
    omega

/-! ## 4. Rigidity from the bare functional equation -/

/-- **Positive-measure Hamburger rigidity from the bare functional equation.** Let `ν ≥ 0` vanish on
`(-∞, 1)` with `∫ u^{-3/2} dν < ∞`. If `Γ_ℝ(s) D_ν(s)` on `Re s = 3/2` and `Γ_ℝ(1 - s) D_ν(1 - s)` on
`Re s = -1/2` agree with `E(s) + α Γ_ℝ(s) + β Γ_ℝ(s - 1)`, where `E` is differentiable on
`-1/2 ≤ Re s ≤ 3/2` and of finite order there, then
`ν = (-2 Re α) · Σ_{k ≥ 0} δ_{k+1}`. -/
theorem measure_eq_of_completed_functional_equation_of_finiteOrder {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν)
    {E : ℂ → ℂ} {α β : ℂ} {C₀ ρ : ℝ}
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hfin : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * measureDirichlet ν s =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 → Complex.Gammaℝ (1 - s) * measureDirichlet ν (1 - s) =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))) :
    β = -α ∧ α.im = 0 ∧ 0 ≤ -2 * α.re ∧
      ν = ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
  set m : ℝ := ∫ u : ℝ, u ^ (-(3 / 2 : ℝ)) ∂ν
  obtain ⟨C₁, hC₁⟩ := exists_decay_Gammaℝ_of_re (a := 3 / 2)
    (ne_neg_two_mul_of_frac (Or.inl rfl))
  obtain ⟨C₂, hC₂⟩ := exists_decay_Gammaℝ_of_re (a := 1 / 2)
    (ne_neg_two_mul_of_frac (Or.inr (Or.inl rfl)))
  obtain ⟨C₃, hC₃⟩ := exists_decay_Gammaℝ_of_re (a := -1 / 2)
    (ne_neg_two_mul_of_frac (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨C₄, hC₄⟩ := exists_decay_Gammaℝ_of_re (a := -3 / 2)
    (ne_neg_two_mul_of_frac (Or.inr (Or.inr (Or.inr rfl))))
  set K₁ : ℝ := C₁ * m + ‖α‖ * C₁ + ‖β‖ * C₂ with hK₁
  set K₂ : ℝ := C₁ * m + ‖α‖ * C₃ + ‖β‖ * C₄ with hK₂
  set K : ℝ := |K₁| + |K₂| with hK
  -- The three-term edge estimate.
  have hedge : ∀ (s w : ℂ) (Ca Cb : ℝ), 0 < 1 + s.im ^ 2 →
      ‖Complex.Gammaℝ w‖ ≤ C₁ / (1 + s.im ^ 2) → ‖measureDirichlet ν w‖ ≤ m →
      ‖Complex.Gammaℝ s‖ ≤ Ca / (1 + s.im ^ 2) → ‖Complex.Gammaℝ (s - 1)‖ ≤ Cb / (1 + s.im ^ 2) →
      ‖Complex.Gammaℝ w * measureDirichlet ν w -
          (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))‖ ≤
        (C₁ * m + ‖α‖ * Ca + ‖β‖ * Cb) / (1 + s.im ^ 2) := by
    intro s w Ca Cb hx hw hD hs1 hs2
    have h0 := norm_sub_le (Complex.Gammaℝ w * measureDirichlet ν w)
      (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))
    have h3 := norm_add_le (α * Complex.Gammaℝ s) (β * Complex.Gammaℝ (s - 1))
    rw [norm_mul] at h0
    rw [norm_mul, norm_mul] at h3
    have ha := mul_le_mul hw hD (norm_nonneg _) ((norm_nonneg _).trans hw)
    have hb := mul_le_mul_of_nonneg_left hs1 (norm_nonneg α)
    have hc := mul_le_mul_of_nonneg_left hs2 (norm_nonneg β)
    have he : C₁ / (1 + s.im ^ 2) * m + ‖α‖ * (Ca / (1 + s.im ^ 2)) +
        ‖β‖ * (Cb / (1 + s.im ^ 2)) = (C₁ * m + ‖α‖ * Ca + ‖β‖ * Cb) / (1 + s.im ^ 2) := by ring
    linarith
  have hRe : ∀ s : ℂ, s.re = 3 / 2 → ‖E s‖ ≤ K / (1 + s.im ^ 2) := by
    intro s hs
    have hx : 0 < 1 + s.im ^ 2 := by positivity
    have hEs : E s = Complex.Gammaℝ s * measureDirichlet ν s -
        (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by rw [hR s hs]; ring
    have h2 : ‖Complex.Gammaℝ (s - 1)‖ ≤ C₂ / (1 + s.im ^ 2) := by
      have h := hC₂ (s - 1) (by rw [Complex.sub_re, Complex.one_re, hs]; norm_num)
      rwa [Complex.sub_im, Complex.one_im, sub_zero] at h
    rw [hEs]
    refine (hedge s s C₁ C₂ hx (hC₁ s hs) (norm_measureDirichlet_le hsupp hs)
      (hC₁ s hs) h2).trans (div_le_div_of_nonneg_right ?_ hx.le)
    exact (le_abs_self K₁).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hLe : ∀ s : ℂ, s.re = -1 / 2 → ‖E s‖ ≤ K / (1 + s.im ^ 2) := by
    intro s hs
    have hx : 0 < 1 + s.im ^ 2 := by positivity
    have h1s : (1 - s).re = 3 / 2 := by rw [Complex.sub_re, Complex.one_re, hs]; norm_num
    have hEs : E s = Complex.Gammaℝ (1 - s) * measureDirichlet ν (1 - s) -
        (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by rw [hL s hs]; ring
    have hw : ‖Complex.Gammaℝ (1 - s)‖ ≤ C₁ / (1 + s.im ^ 2) := by
      have h := hC₁ (1 - s) h1s
      rwa [Complex.sub_im, Complex.one_im, zero_sub, neg_sq] at h
    have h4 : ‖Complex.Gammaℝ (s - 1)‖ ≤ C₄ / (1 + s.im ^ 2) := by
      have h := hC₄ (s - 1) (by rw [Complex.sub_re, Complex.one_re, hs]; norm_num)
      rwa [Complex.sub_im, Complex.one_im, sub_zero] at h
    rw [hEs]
    refine (hedge s (1 - s) C₃ C₄ hx hw (norm_measureDirichlet_le hsupp h1s)
      (hC₃ s hs) h4).trans (div_le_div_of_nonneg_right ?_ hx.le)
    exact (le_abs_self K₂).trans (le_add_of_nonneg_left (abs_nonneg _))
  have hdecay := norm_le_of_edges_of_finiteOrder hE hfin hRe hLe
  exact measure_eq_of_completed_functional_equation hsupp hmom hE hdecay hR hL

end GaloisForLFunctions.ArithmeticPositiveDuality
