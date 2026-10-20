import GaloisForLFunctions.SquareRootThreshold.NegativityRateEqualsMaximalDepth
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# Even and odd two-bump tests decide the critical line

The unimodular two-bump criterion uses the tests `b(t + v/2) + τ b(t − v/2)` for all `|τ| = 1`.
The two real directions `τ = ±1` already suffice.

* **The lag structure is an exponential sum over the zeros** (`lagStructure_eq_tsum_lagCoeff`):
  `S(v) = Σ_z F(z) e^{zv}`, with `F(z) = m_ρ h_k(γ_ρ)` at the zero `ρ = ½ + z`. Reflection
  symmetry gives `conj S(−v) = S(v)` (`conj_lagStructure_neg`). Hence
  `2 Re S(v) = Σ_z D(z) e^{zv}` with `D(z) = F(z) + conj F(z̄)` (`two_re_lagStructure_eq`).
* **Even and odd tests bound `Re S`** (`abs_re_lagStructure_le`). The even and odd tests have
  `Re W = 2 Re S(0) ± 2 Re S(v)`. Their positivity at every lag `v ≥ 0` keeps the exponential sum
  `Σ_z D(z) e^{zv}` bounded.
* **No top pole** (`evenCoeff_eq_zero_of_evenOdd_nonneg`). By the Laplace argument
  (`eq_zero_of_norm_tsum_exp_le_exp`), every exponent `z` with `Re z > 0` then has `D(z) = 0`.
* **No cancellation** (`exists_center_evenCoeff_ne_zero`). For the bump `κ_w` modulated to the
  center `γ_c` and a zero `t = ½ + δ + iγ` right of the line,
  `D = m h(x − iδ)² + m* h(2γ − x − iδ)²`. Here `x = γ − γ_c`, `h` is the transform of `κ_w`, and
  `m*` is the multiplicity of `t̄`. If `D` vanished for every center, then `φ(x) = |h(x − iδ)|²`
  would satisfy `m φ(x) = m* φ(x − 2γ)`. Iterating this keeps `φ` at least `φ(0) > 0` along
  `x = ±2nγ`, against the decay of `h`.

**Two parameters decide the line** (`onLine_iff_evenOdd_twoBump_nonneg`). A tempered configuration
has all its zeros on the critical line iff `Re W ≥ 0` on every test `κ_γ(t + v/2) ± κ_γ(t − v/2)`,
`γ ∈ ℝ`, `v ≥ 0`. For `ζ` this reads on the prime side
(`onLine_iff_primeSide_evenOdd_twoBump_nonneg`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The lag structure as an exponential sum over the zeros -/

/-- The coefficient `F(z) = m_ρ h_k(γ_ρ)` of the zero `ρ = ½ + z` in the lag structure of `b`,
`k = b ⋆ b̃`, and `0` off the carrier. -/
def lagCoeff (Z : ZeroConfig) (b : ℝ → ℂ) (z : ℂ) : ℂ :=
  Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b) (gammaOf ρ))
    (1 / 2 + z)

theorem I_mul_gammaOf_half_add (z : ℂ) : I * gammaOf (1 / 2 + z) = z := by
  simp only [gammaOf, add_sub_cancel_left]
  field_simp

theorem gammaOf_reflect_eq_conj (ρ : ℂ) : gammaOf (reflect ρ) = conj (gammaOf ρ) := by
  apply Complex.ext
  · simp [gammaOf, reflect]
  · simp [gammaOf, reflect]; ring

/-- **`S(v) = Σ_z F(z) e^{zv}`**, summed over `ℂ`. -/
theorem lagStructure_eq_tsum_lagCoeff (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    Summable (fun z : ℂ => lagCoeff Z b z * cexp (z * v)) ∧
      lagStructure Z b v = ∑' z : ℂ, lagCoeff Z b z * cexp (z * v) := by
  set g : ℂ → ℂ := Z.carrier.indicator fun ρ =>
    (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b) (gammaOf ρ) * cexp (I * gammaOf ρ * v) with hg
  have hgs : Summable g := summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs v)
  have hcomp : (fun z : ℂ => lagCoeff Z b z * cexp (z * v)) = g ∘ Equiv.addLeft (1 / 2 : ℂ) := by
    funext z
    simp only [Function.comp, Equiv.coe_addLeft, lagCoeff, hg]
    by_cases h : (1 / 2 + z) ∈ Z.carrier
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, I_mul_gammaOf_half_add]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  refine ⟨hcomp ▸ (Equiv.summable_iff _).mpr hgs, ?_⟩
  rw [hcomp, lagStructure]
  exact (tsum_subtype Z.carrier fun ρ => (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b) (gammaOf ρ) *
    cexp (I * gammaOf ρ * v)).trans (Equiv.tsum_eq (Equiv.addLeft (1 / 2 : ℂ)) g).symm

/-- **Reflection.** `F(−z̄) = conj F(z)`: the zero `½ − z̄` is the reflection of `½ + z`. -/
theorem lagCoeff_neg_conj (Z : ZeroConfig) {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (z : ℂ) : lagCoeff Z b (-conj z) = conj (lagCoeff Z b z) := by
  have hr : (1 / 2 + -conj z : ℂ) = reflect (1 / 2 + z) := by
    apply Complex.ext
    · simp [reflect]; ring
    · simp [reflect]
  unfold lagCoeff
  rw [hr]
  by_cases h : (1 / 2 + z) ∈ Z.carrier
  · rw [Set.indicator_of_mem (Z.reflect_mem _ h), Set.indicator_of_mem h, Z.mult_reflect _ h,
      map_mul, Complex.conj_natCast, gammaOf_reflect_eq_conj, EF.paperFT_weilTest hb hb hbc hbc,
      EF.paperFT_weilTest hb hb hbc hbc, Complex.conj_conj, map_mul, Complex.conj_conj]
    ring
  · rw [Set.indicator_of_notMem fun h' => h ((reflect_mem_iff Z _).mp h'),
      Set.indicator_of_notMem h, map_zero]

/-- **Reflection symmetry of the lag structure:** `conj S(−v) = S(v)`. -/
theorem conj_lagStructure_neg (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    conj (lagStructure Z b (-v)) = lagStructure Z b v := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  rw [(lagStructure_eq_tsum_lagCoeff Z hZ hb hbs (-v)).2,
    (lagStructure_eq_tsum_lagCoeff Z hZ hb hbs v).2, Complex.conj_tsum]
  set σ : ℂ ≃ ℂ := ⟨fun z => -conj z, fun z => -conj z, fun z => by simp, fun z => by simp⟩
  rw [← σ.tsum_eq]
  refine tsum_congr fun z => ?_
  show conj (lagCoeff Z b (-conj z) * cexp (-conj z * ((-v : ℝ) : ℂ))) =
    lagCoeff Z b z * cexp (z * v)
  rw [lagCoeff_neg_conj Z hb.continuous hbc, map_mul, Complex.conj_conj, ← Complex.exp_conj]
  congr 2
  simp [map_mul, Complex.conj_ofReal]

/-- The merged coefficient `D(z) = F(z) + conj F(z̄)` of `e^{zv}` in `2 Re S(v)`. -/
def evenCoeff (Z : ZeroConfig) (b : ℝ → ℂ) (z : ℂ) : ℂ :=
  lagCoeff Z b z + conj (lagCoeff Z b (conj z))

/-- **`2 Re S(v) = Σ_z D(z) e^{zv}`.** -/
theorem two_re_lagStructure_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    Summable (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) ∧
      ((2 * (lagStructure Z b v).re : ℝ) : ℂ) =
        ∑' z : ℂ, evenCoeff Z b z * cexp (z * v) := by
  obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs v
  set σ : ℂ ≃ ℂ := ⟨fun z => conj z, fun z => conj z, fun z => by simp, fun z => by simp⟩
  have hconj : (fun z : ℂ => conj (lagCoeff Z b (conj z)) * cexp (z * v)) =
      (fun z => conj (lagCoeff Z b z * cexp (z * v))) ∘ σ := by
    funext z
    simp only [Function.comp, σ, Equiv.coe_fn_mk, map_mul, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_conj]
  have hs' : Summable fun z : ℂ => conj (lagCoeff Z b (conj z)) * cexp (z * v) := by
    rw [hconj, Equiv.summable_iff]
    exact hs.map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj
  have hsum : (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) = fun z =>
      lagCoeff Z b z * cexp (z * v) + conj (lagCoeff Z b (conj z)) * cexp (z * v) := by
    funext z; rw [evenCoeff, add_mul]
  refine ⟨hsum ▸ hs.add hs', ?_⟩
  rw [hsum, hs.tsum_add hs', ← Complex.add_conj, he, Complex.conj_tsum, hconj]
  exact congrArg _ (Equiv.tsum_eq σ fun z => conj (lagCoeff Z b z * cexp (z * v))).symm

/-- **Even and odd tests bound `Re S`.** If the tests `b(t + v/2) ± b(t − v/2)` have nonnegative
Weil form, then `|Re S(v)| ≤ Re S(0)`. -/
theorem abs_re_lagStructure_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hp : 0 ≤ (Z.W (twoBump b v 1) (twoBump b v 1)).re)
    (hm : 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re) :
    |(lagStructure Z b v).re| ≤ (lagStructure Z b 0).re := by
  have hX : lagStructure Z b v + conj (lagStructure Z b (-v)) = 2 * lagStructure Z b v := by
    rw [conj_lagStructure_neg Z hZ hb hbs v]; ring
  rw [re_W_unit_twoBump Z hZ hb hbs v (by simp), hX] at hp
  rw [re_W_unit_twoBump Z hZ hb hbs v (by simp), hX] at hm
  simp only [one_mul, neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### No top pole -/

theorem mem_of_evenCoeff_ne_zero {Z : ZeroConfig} {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff Z b z ≠ 0) : (1 / 2 + z) ∈ Z.carrier ∨ (1 / 2 + conj z) ∈ Z.carrier := by
  by_contra h
  push Not at h
  exact hz (by rw [evenCoeff, lagCoeff, lagCoeff, Set.indicator_of_notMem h.1,
    Set.indicator_of_notMem h.2, map_zero, add_zero])

theorem re_le_of_evenCoeff_ne_zero {Z : ZeroConfig} {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff Z b z ≠ 0) : z.re ≤ 1 / 2 := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · have := (Z.strip _ h).2; simp at this; linarith
  · have := (Z.strip _ h).2; simp at this; linarith

/-- The exponents of `2 Re S` form a countable set. -/
theorem countable_evenCoeff_support (Z : ZeroConfig) (b : ℝ → ℂ) :
    {z : ℂ | evenCoeff Z b z ≠ 0}.Countable := by
  refine (((carrier_countable Z).image fun ρ => ρ - 1 / 2).union
    ((carrier_countable Z).image fun ρ => conj (ρ - 1 / 2))).mono fun z hz => ?_
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact Or.inl ⟨1 / 2 + z, h, by ring⟩
  · exact Or.inr ⟨1 / 2 + conj z, h, by simp⟩

/-- Finitely many exponents of `2 Re S` lie on each horizontal line. -/
theorem finite_evenCoeff_line (Z : ZeroConfig) (b : ℝ → ℂ) (γ : ℝ) :
    {z : ℂ | evenCoeff Z b z ≠ 0 ∧ z.im = γ}.Finite := by
  have h1 := (Z.finite_window (γ - 1) (γ + 1)).image fun ρ : ℂ => ρ - 1 / 2
  have h2 := (Z.finite_window (-γ - 1) (-γ + 1)).image fun ρ : ℂ => conj (ρ - 1 / 2)
  refine (h1.union h2).subset fun z hz => ?_
  have hz' : evenCoeff Z b z ≠ 0 ∧ z.im = γ := hz
  rcases mem_of_evenCoeff_ne_zero hz'.1 with h | h
  · refine Or.inl ⟨1 / 2 + z, ⟨h, ?_⟩, by simp⟩
    have : (1 / 2 + z).im = γ := by simp [hz'.2]
    exact ⟨by linarith, by linarith⟩
  · refine Or.inr ⟨1 / 2 + conj z, ⟨h, ?_⟩, by simp⟩
    have : (1 / 2 + conj z).im = -γ := by simp [hz'.2]
    exact ⟨by linarith, by linarith⟩

/-- **No top pole.** If the even and odd two-bump tests of `b` are Weil nonnegative at every lag
`v ≥ 0`, then `D(z) = 0` for every exponent with `Re z > 0`. -/
theorem evenCoeff_eq_zero_of_evenOdd_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    (hp : ∀ v : ℝ, 0 ≤ v → 0 ≤ (Z.W (twoBump b v 1) (twoBump b v 1)).re)
    (hm : ∀ v : ℝ, 0 ≤ v → 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z : ℂ} (hz : 0 < z.re) : evenCoeff Z b z = 0 := by
  classical
  by_contra hne
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  -- the rightmost exponent on the line of `z`
  set L := (finite_evenCoeff_line Z b z.im).toFinset with hL
  obtain ⟨z₀, hz₀L, hmax⟩ := L.exists_max_image Complex.re
    ⟨z, (Set.Finite.mem_toFinset _).mpr ⟨hne, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z.re ≤ z₀.re := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hne, rfl⟩)
  -- separation of the line of `z₀`
  obtain ⟨η₁, hη₁, hsep₁⟩ := exists_sep_height Z z₀.im
  obtain ⟨η₂, hη₂, hsep₂⟩ := exists_sep_height Z (-z₀.im)
  have hsep : ∀ t : ι, |(t : ℂ).im - z₀.im| < min η₁ η₂ → (t : ℂ).im = z₀.im := fun t ht => by
    rcases mem_of_evenCoeff_ne_zero t.2 with h | h
    · have := hsep₁ _ h (by simpa using ht.trans_le (min_le_left _ _))
      simpa using this
    · have := hsep₂ _ h (by
        rw [show (1 / 2 + conj (t : ℂ)).im - -z₀.im = -((t : ℂ).im - z₀.im) by simp; ring,
          abs_neg]
        exact ht.trans_le (min_le_right _ _))
      simp at this; linarith
  -- the summable coefficients and the bound
  have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hD : Summable fun t : ι => ‖evenCoeff Z b t‖ := hD0.subtype ι
  have hK : ∀ v : ℝ, 0 ≤ v → ‖∑' t : ι, evenCoeff Z b t * cexp ((t : ℂ) * v)‖ ≤
      2 * (lagStructure Z b 0).re * Real.exp (0 * v) := by
    intro v hv
    have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * v) = 0 by rw [h0, zero_mul])
    rw [tsum_subtype_eq_of_support_subset hsub, ← (two_re_lagStructure_eq Z hZ hb hbs v).2, Complex.norm_real, Real.norm_eq_abs, zero_mul,
      Real.exp_zero, mul_one, abs_mul, abs_two]
    linarith [abs_re_lagStructure_le Z hZ hb hbs (hp v hv) (hm v hv)]
  have h := eq_zero_of_norm_tsum_exp_le_exp (ι := ι) (lam := fun t => (t : ℂ))
    (q := fun t => evenCoeff Z b t) hD (A := 1 / 2) (fun t => re_le_of_evenCoeff_ne_zero t.2)
    (σ := 0) ⟨z₀, hz₀⟩ (by simp; linarith)
    (fun t ht => hmax t ((Set.Finite.mem_toFinset _).mpr ⟨t.2, ht.trans him₀⟩))
    (fun t ht => Subtype.ext ht) (lt_min hη₁ hη₂) hsep hK
  exact hz₀ h

/-! ### No cancellation -/

/-- The transform of `κ_w` is even. -/
theorem paperFT_scaledBump_neg (w : ℝ) (z : ℂ) :
    paperFT (scaledBump w) (-z) = paperFT (scaledBump w) z :=
  Taper.paperFT_neg_of_even (v := fun u => weilBump (u / (4 * w)))
    (fun u => by simp only [neg_div, weilBump.neg]) z

/-- The transform of `κ_w` commutes with conjugation. -/
theorem conj_paperFT_scaledBump (w : ℝ) (z : ℂ) :
    conj (paperFT (scaledBump w) z) = paperFT (scaledBump w) (conj z) := by
  rw [← paperFT_scaledBump_neg w (conj z)]
  exact Taper.conj_paperFT_ofReal (fun u => weilBump (u / (4 * w))) z

theorem gammaOf_half_add (z : ℂ) : gammaOf (1 / 2 + z) = -(I * z) := by
  rw [gammaOf, add_sub_cancel_left, Complex.div_I]
  ring

/-- For `κ_w` modulated to `c`, the coefficient of the zero `½ + z` is `m h(−iz − c)²`. -/
theorem lagCoeff_modScaledBump (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ}
    (hz : (1 / 2 + z) ∈ Z.carrier) :
    lagCoeff Z (modScaledBump w c) z =
      (Z.mult (1 / 2 + z) : ℂ) * paperFT (scaledBump w) (-(I * z) - c) ^ 2 := by
  have hbc : HasCompactSupport (modScaledBump w c) :=
    hasCompactSupport_of_support_subset_abs (modScaledBump_support hw c)
  have hcont := (contDiff_modScaledBump_two w c).continuous
  rw [lagCoeff, Set.indicator_of_mem hz, EF.paperFT_weilTest hcont hcont hbc hbc,
    paperFT_modScaledBump, paperFT_modScaledBump, conj_paperFT_scaledBump, gammaOf_half_add]
  simp only [map_sub, map_neg, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring_nf

/-- **No cancellation.** For a zero `½ + z`, some center `c` gives `D(z) ≠ 0` for the bump `κ_w`
modulated to `c`. -/
theorem exists_center_evenCoeff_ne_zero (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) {z : ℂ}
    (hz : (1 / 2 + z) ∈ Z.carrier) : ∃ c : ℝ, evenCoeff Z (modScaledBump w c) z ≠ 0 := by
  classical
  set h := paperFT (scaledBump w) with hh
  set δ := z.re
  set γ := z.im
  set m : ℝ := (Z.mult (1 / 2 + z) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Z.one_le_mult _ hz
  set ms : ℝ := if (1 / 2 + conj z) ∈ Z.carrier then (Z.mult (1 / 2 + conj z) : ℝ) else 0 with hms
  have hms0 : 0 ≤ ms := by rw [hms]; split_ifs <;> positivity
  -- the merged coefficient as a function of `x = γ − c`
  have hD : ∀ x : ℝ, evenCoeff Z (modScaledBump w (γ - x)) z =
      m * h ((x : ℂ) - I * δ) ^ 2 + ms * h ((x - 2 * γ : ℝ) + I * δ) ^ 2 := by
    intro x
    have hz1 : -(I * z) - ((γ - x : ℝ) : ℂ) = (x : ℂ) - I * δ := by
      apply Complex.ext <;> simp [δ, γ]
    have hz2 : I * z - ((γ - x : ℝ) : ℂ) = ((x - 2 * γ : ℝ) : ℂ) + I * δ := by
      apply Complex.ext <;> simp [δ, γ]
      ring
    rw [evenCoeff, lagCoeff_modScaledBump Z hw _ hz, hz1]
    congr 1
    rw [hms]
    split_ifs with hzc
    · rw [lagCoeff_modScaledBump Z hw _ hzc, map_mul, Complex.conj_natCast, map_pow,
        conj_paperFT_scaledBump]
      simp only [map_sub, map_neg, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
      rw [show -(-I * z) - ((γ - x : ℝ) : ℂ) = I * z - ((γ - x : ℝ) : ℂ) by ring, hz2]
      push_cast
      ring
    · rw [lagCoeff, Set.indicator_of_notMem hzc, map_zero]
      push_cast
      ring
  -- `φ(0) > 0`
  have hpos : 0 < ‖h (-(I * δ))‖ := by
    have h1 := norm_paperFT_scaledBump_I_mul_ge hw (-δ)
    have h2 : (0 : ℝ) < ∫ u, weilBump u := weilBump.integral_pos
    have e : ((-δ : ℝ) : ℂ) * I = -(I * δ) := by push_cast; ring
    rw [e] at h1
    exact lt_of_lt_of_le (by positivity) h1
  by_contra hall
  push Not at hall
  have h0 : ∀ x : ℝ, m * h ((x : ℂ) - I * δ) ^ 2 + ms * h ((x - 2 * γ : ℝ) + I * δ) ^ 2 = 0 :=
    fun x => (hD x).symm.trans (hall _)
  have hreflect : ∀ y : ℝ, ‖h ((y : ℂ) + I * δ)‖ = ‖h ((y : ℂ) - I * δ)‖ := fun y => by
    rw [← Complex.norm_conj, conj_paperFT_scaledBump]
    congr 2
    simp [map_add, map_mul]
    ring
  -- the relation `m φ(x) = ms φ(x − 2γ)`
  set φ : ℝ → ℝ := fun x => ‖h ((x : ℂ) - I * δ)‖ ^ 2 with hφ
  have hrel : ∀ x : ℝ, m * φ x = ms * φ (x - 2 * γ) := fun x => by
    have := congrArg norm (eq_neg_of_add_eq_zero_left (h0 x))
    rw [norm_neg, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_nonneg hms0,
      hreflect] at this
    simpa [hφ] using this
  have hφ0 : 0 < φ 0 := by
    simp only [hφ, Complex.ofReal_zero, zero_sub]
    positivity
  -- height zero: the zero is its own conjugate
  by_cases hγ : γ = 0
  · have hzc : conj z = z := Complex.ext (by simp) (by simp [hγ, γ])
    have hmsm : ms = m := by rw [hms, if_pos (by rw [hzc]; exact hz), hzc]
    have h00 := h0 0
    have he : h (-(I * δ)) = h (I * δ) := paperFT_scaledBump_neg w _
    have e1 : ((0 : ℝ) : ℂ) - I * δ = -(I * δ) := by simp
    have e2 : (((0 : ℝ) - 2 * γ : ℝ) : ℂ) + I * δ = I * δ := by simp [hγ]
    rw [e1, e2, he, hmsm] at h00
    rw [he] at hpos
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by linarith : m ≠ 0)
    have h2 : (2 * (m : ℂ)) * h (I * δ) ^ 2 = 0 := by linear_combination h00
    exact mul_ne_zero (mul_ne_zero two_ne_zero hm0) (pow_ne_zero 2 (norm_pos_iff.mp hpos)) h2
  -- otherwise `φ` does not decay along `±2nγ`
  have hms_pos : 0 < ms := by
    by_contra hle
    have hms' : ms = 0 := le_antisymm (not_lt.mp hle) hms0
    have := hrel 0
    rw [hms', zero_mul] at this
    nlinarith
  obtain ⟨s, hs, hgrow⟩ : ∃ s : ℝ, |s| = 2 * |γ| ∧ ∀ n : ℕ, φ 0 ≤ φ (n * s) := by
    have hφnn : ∀ x, 0 ≤ φ x := fun x => by simp only [hφ]; positivity
    rcases le_or_gt ms m with hle | hlt
    · refine ⟨-(2 * γ), by rw [abs_neg, abs_mul, abs_two], fun n => ?_⟩
      induction n with
      | zero => simp
      | succ n ih =>
        have hr := hrel (n * -(2 * γ))
        have hstep : φ (n * -(2 * γ)) ≤ φ ((n + 1 : ℕ) * -(2 * γ)) := by
          have e : (n * -(2 * γ)) - 2 * γ = ((n + 1 : ℕ) : ℝ) * -(2 * γ) := by push_cast; ring
          rw [e] at hr
          nlinarith [hφnn (n * -(2 * γ)), hφnn (((n + 1 : ℕ) : ℝ) * -(2 * γ))]
        exact ih.trans hstep
    · refine ⟨2 * γ, by rw [abs_mul, abs_two], fun n => ?_⟩
      induction n with
      | zero => simp
      | succ n ih =>
        have hr := hrel ((n + 1 : ℕ) * (2 * γ))
        have e : ((n + 1 : ℕ) : ℝ) * (2 * γ) - 2 * γ = n * (2 * γ) := by push_cast; ring
        rw [e] at hr
        nlinarith [hφnn (n * (2 * γ)), hφnn (((n + 1 : ℕ) : ℝ) * (2 * γ))]
  -- decay of `φ`
  set B := Real.exp (|δ| * w) * (4 * ((∫ u, ‖scaledBump w u‖) +
    ∫ u, ‖deriv (deriv (scaledBump w)) u‖)) with hB
  have hdecay : ∀ y : ℝ, φ y ≤ B ^ 2 / (1 + |y|) := fun y => by
    have hc2 : ContDiff ℝ 2 (scaledBump w) := (contDiff_scaledBump w).of_le (by norm_num)
    have hsupp : ∀ u, scaledBump w u ≠ 0 → |u| ≤ w := fun u hu => by
      by_contra h'; exact hu (scaledBump_eq_zero hw (not_le.mp h').le)
    have hd := norm_paperFT_le_decay hc2 hsupp ((y : ℂ) - I * δ)
    have him : |((y : ℂ) - I * δ).im| = |δ| := by simp
    have hre : |((y : ℂ) - I * δ).re| = |y| := by simp
    rw [him, hre, ← hB] at hd
    have h1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
    have hB0 : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num)
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)))
    simp only [hφ]
    calc ‖h ((y : ℂ) - I * δ)‖ ^ 2 ≤ (B / (1 + |y|) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hd 2
      _ = B ^ 2 / (1 + |y|) ^ 4 := by rw [div_pow, ← pow_mul]
      _ ≤ B ^ 2 / (1 + |y|) := div_le_div_of_nonneg_left (sq_nonneg B) (by positivity)
          (le_self_pow₀ h1 (by norm_num))
  -- a far point of the progression contradicts the decay
  have hγpos : 0 < |γ| := abs_pos.mpr hγ
  obtain ⟨n, hn⟩ := exists_nat_gt (B ^ 2 / (φ 0 * (2 * |γ|)))
  have hfar := (hgrow n).trans (hdecay (n * s))
  have habs : |(n : ℝ) * s| = n * (2 * |γ|) := by rw [abs_mul, Nat.abs_cast, hs]
  rw [habs, le_div_iff₀ (by positivity)] at hfar
  rw [div_lt_iff₀ (by positivity)] at hn
  nlinarith

/-! ### Two parameters decide the line -/

/-- **Two parameters decide the line.** A tempered configuration has all its zeros on the critical
line iff its Weil form is nonnegative on every even and every odd two-bump test
`κ_γ(t + v/2) ± κ_γ(t − v/2)`, `γ ∈ ℝ`, `v ≥ 0`. -/
theorem onLine_iff_evenOdd_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ (γ v : ℝ) (ε : ℂ), 0 ≤ v → (ε = 1 ∨ ε = -1) →
      0 ≤ (Z.W (twoBump (modScaledBump 1 γ) v ε) (twoBump (modScaledBump 1 γ) v ε)).re := by
  refine ⟨fun hon _ _ _ _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  have hz : (1 / 2 + (t - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact ht.1
  have hzre : 0 < (t - 1 / 2).re := by simp; linarith [ht.2]
  obtain ⟨c, hc⟩ := exists_center_evenCoeff_ne_zero Z one_pos hz
  exact hc (evenCoeff_eq_zero_of_evenOdd_nonneg Z hZ (contDiff_modScaledBump_two 1 c)
    (modScaledBump_support one_pos c) (fun v hv => h c v 1 hv (Or.inl rfl))
    (fun v hv => h c v (-1) hv (Or.inr rfl)) hzre)

/-- **For `ζ`, on the prime side.** RH holds iff the prime-side functional is nonnegative on the
autocorrelations of the even and odd two-bump tests `κ_γ(t + v/2) ± κ_γ(t − v/2)`. -/
theorem onLine_iff_primeSide_evenOdd_twoBump_nonneg :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (ε : ℂ), 0 ≤ v → (ε = 1 ∨ ε = -1) →
        0 ≤ (EF.literatureRHS (EF.weilTest (twoBump (modScaledBump 1 γ) v ε)
          (twoBump (modScaledBump 1 γ) v ε))).re := by
  refine (onLine_iff_evenOdd_twoBump_nonneg _ temperedConfig_zetaZeroConfig).trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun ε => ?_
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump 1 γ) v ε)
    (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, ε])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support one_pos γ)) v ε)]

end GaloisForLFunctions.SquareRootThreshold
