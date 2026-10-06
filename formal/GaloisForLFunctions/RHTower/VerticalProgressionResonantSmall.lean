import GaloisForLFunctions.RHTower.VerticalProgressionResonantCount

/-!
# Resonant ratios with small denominators

Fix `0 < θ < ½`, `η = (½ − θ)/4`, `N = ⌊T^θ⌋`, the phase width `δ = T^{−1+η}` and the size cut
`Y = T^{1−2η}`. A ratio `c = a/b` is *small resonant* if `|u(c) − j| < δ` for some `j ≠ 0` and
`ab < Y`.

**Theorem** (`tendsto_smallResonant_div`). `T^{−1} Σ_{c small resonant} ‖Φ_T(c)‖ → 0`.

**Proof.** Group the ratios by `j = round u(c)`.
* *Uniqueness*: the `j`-resonant coprime pairs with `ab < Y` number at most `2e³δ'Y + 1 < 2`
  (`card_window_le`), so each group has at most one ratio.
* *Domination*: `‖Φ_T(c)‖/T ≤ 2Ψ₀ (ab)^{−1/2} C(ab)^{1/3}` and `ab ≥ e^{2π|j|/α − 1}`, a summable
  geometric bound in `j`.
* *Pointwise limit*: for fixed `j` and `X₀`, ratios with `ab ≤ X₀` and `u(c) ≠ j` leave the window,
  the exact resonance `u(c) = j` (if any) has `F(c, t) → 0`, and ratios with `ab > X₀` are
  `≤ 2Ψ₀ C X₀^{−1/6}`. Dominated convergence over `j ∈ ℤ` concludes.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)

/-! ## Summability of the fibre terms -/

theorem summable_norm_fiberTerm {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ}
    (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) :
    Summable (fun c : ℕ × ℕ => ‖fiberTerm ψ α β N T c‖) := by
  have hm : ∀ h k : ℕ, HasSum (fun c : ℕ × ℕ =>
      ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c}, ‖quadTerm ψ α β N T P h k‖)
        (∑' P : ℕ × ℕ, ‖quadTerm ψ α β N T P h k‖) := fun h k =>
    (summable_norm_quadTerm hsupp N hT hpos h k).hasSum.tsum_fiberwise (fun P => quadRatio P h k)
  have hsm : Summable (fun c : ℕ × ℕ => ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c}, ‖quadTerm ψ α β N T P h k‖) :=
    summable_sum fun h _ => summable_sum fun k _ => (hm h k).summable
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_) hsm
  unfold fiberTerm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  exact norm_tsum_le_tsum_norm ((summable_norm_quadTerm hsupp N hT hpos h k).subtype _)

/-! ## Elementary lemmas -/

theorem tsum_le_of_subsingleton_support {ι : Type*} {f : ι → ℝ}
    (hs : (Function.support f).Subsingleton) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, f x ≤ B) :
    ∑' x, f x ≤ B := by
  rcases hs.eq_empty_or_singleton with h | ⟨x₀, h⟩
  · have : f = 0 := by
      funext x; by_contra hx
      have : x ∈ Function.support f := hx
      rw [h] at this; exact this
    rw [this]; simpa using hB
  · rw [tsum_eq_single x₀ (fun x hx => by
      by_contra hfx
      have : x ∈ Function.support f := hfx
      rw [h] at this; exact hx this)]
    exact hf x₀

theorem round_eq_of_abs_sub_lt {u : ℝ} {j : ℤ} (h : |u - j| < 1 / 2) : round u = j := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith [(abs_lt.mp h).1, (abs_lt.mp h).2]

theorem ratioPhase_eq (α : ℝ) (c : ℕ × ℕ) : ratioPhase α c = α * ratioLog c / (2 * Real.pi) := rfl

theorem abs_ratioLog_le_log {c : ℕ × ℕ} (ha : 0 < c.1) (hb : 0 < c.2) :
    |ratioLog c| ≤ Real.log ((c.1 * c.2 : ℕ) : ℝ) := by
  have haR : (1 : ℝ) ≤ c.1 := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ c.2 := by exact_mod_cast hb
  unfold ratioLog
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  have := Real.log_nonneg haR
  have := Real.log_nonneg hbR
  rw [abs_le]; constructor <;> linarith

/-- `|u(c) − j| < δ` is `|λ(c) − 2πj/α| < 2πδ/α`. -/
theorem abs_ratioLog_sub_lt {α δ : ℝ} (hα : 0 < α) {c : ℕ × ℕ} {j : ℤ}
    (h : |ratioPhase α c - j| < δ) :
    |ratioLog c - 2 * Real.pi * j / α| < 2 * Real.pi * δ / α := by
  rw [ratioPhase_eq] at h
  have e : ratioLog c - 2 * Real.pi * j / α = (2 * Real.pi / α) * (α * ratioLog c / (2 * Real.pi) - j) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity), show 2 * Real.pi * δ / α = (2 * Real.pi / α) * δ by
    ring]
  exact mul_lt_mul_of_pos_left h (by positivity)

/-- A `j`-resonant pair has `ab ≥ e^{2π|j|/α − δ'}`. -/
theorem exp_le_of_resonant {α δ' : ℝ} (hα : 0 < α) {c : ℕ × ℕ} (ha : 0 < c.1) (hb : 0 < c.2)
    {j : ℤ} (h : |ratioLog c - 2 * Real.pi * j / α| < δ') :
    Real.exp (2 * Real.pi * |(j : ℝ)| / α - δ') ≤ ((c.1 * c.2 : ℕ) : ℝ) := by
  have hab : (0 : ℝ) < ((c.1 * c.2 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hb
  rw [← Real.exp_log hab]
  apply Real.exp_le_exp.mpr
  have h1 := abs_ratioLog_le_log ha hb
  have h2 : 2 * Real.pi * |(j : ℝ)| / α = |2 * Real.pi * j / α| := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hα]
  rw [h2]
  have := abs_sub_abs_le_abs_sub (2 * Real.pi * j / α) (ratioLog c)
  rw [abs_sub_comm] at h
  linarith

/-! ## The small resonant ratios -/

/-- The exponent `η = (½ − θ)/4`. -/
def resExp (θ : ℝ) : ℝ := (1 / 2 - θ) / 4

/-- The small resonant ratios at height `T`: `|u(c) − j| < T^{−1+η}` for some `j ≠ 0`, `ab < T^{1−2η}`. -/
def smallResonant (α θ T : ℝ) : Set (ℕ × ℕ) :=
  {c | (∃ j : ℤ, j ≠ 0 ∧ |ratioPhase α c - j| < T ^ (-1 + resExp θ)) ∧
    ((c.1 * c.2 : ℕ) : ℝ) < T ^ (1 - 2 * resExp θ)}

theorem rpow_neg_sixth_le {x L : ℝ} (hx : Real.exp L ≤ x) :
    x ^ (-(1 / 6) : ℝ) ≤ Real.exp (-(L / 6)) := by
  calc x ^ (-(1 / 6) : ℝ) ≤ (Real.exp L) ^ (-(1 / 6) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos L) hx (by norm_num)
    _ = Real.exp (-(L / 6)) := by rw [← Real.exp_mul]; ring_nf

/-- `‖Φ_T(c)‖/T ≤ 2Ψ₀ C (ab)^{−1/6}` from the polynomial envelope. -/
theorem fiberTerm_div_le {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β : ℝ} (N : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, ψ (x / T) ≠ 0 → ‖ratioForm N a b (α * x + β)‖ ≤ M) :
    ‖fiberTerm ψ α β N T (a, b)‖ / T ≤ 2 * Ψ₀ * ((Real.sqrt ((a : ℝ) * b))⁻¹ * M) := by
  have hT0 : 0 < T := by linarith
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  have h := norm_fiberTerm_le hsupp hΨ N hT0 hpos hab ha hb hM0 hM
  rw [div_le_iff₀ hT0]
  have hx : 0 ≤ Ψ₀ * ((Real.sqrt ((a : ℝ) * b))⁻¹ * M) := by positivity
  nlinarith

theorem sqrt_inv_mul_rpow {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * x ^ (1 / 3 : ℝ) = x ^ (-(1 / 6) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  norm_num

/-- **Small resonant ratios are negligible.** -/
theorem tendsto_smallResonant_div {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {Ψ₀ : ℝ} (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun T => ∑' c, (smallResonant α θ T).indicator
      (fun c => ‖fiberTerm ψ α β (molLen θ T) T c‖ / T) c) atTop (𝓝 0) := by
  set η := resExp θ with hηdef
  have hη : 0 < η := by rw [hηdef]; unfold resExp; linarith
  have hη8 : η < 1 / 8 := by rw [hηdef]; unfold resExp; linarith
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  obtain ⟨CU, hCU0, hU⟩ := exists_norm_ratioForm_le hθ0 hθ (c₁ := α / 2) (c₂ := 3 * α)
    (by positivity) (by linarith)
  set δ : ℝ → ℝ := fun T => T ^ (-1 + η)
  set Y : ℝ → ℝ := fun T => T ^ (1 - 2 * η)
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_rpow_of_neg (by linarith)
  -- the uniqueness window `2e³δ'Y < 1`
  have hunique : Tendsto (fun T => 2 * Real.exp 3 * (2 * Real.pi * δ T / α) * Y T) atTop (𝓝 0) := by
    have h := (tendsto_rpow_of_neg (show -η < 0 by linarith)).const_mul
      (2 * Real.exp 3 * (2 * Real.pi / α))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [δ, Y]
    rw [show 2 * Real.exp 3 * (2 * Real.pi * T ^ (-1 + η) / α) * T ^ (1 - 2 * η) =
      2 * Real.exp 3 * (2 * Real.pi / α) * (T ^ (-1 + η) * T ^ (1 - 2 * η)) by ring,
      ← Real.rpow_add hT]
    ring_nf
  -- the basic eventual conditions
  have hgood : ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 2 * |β| ≤ α * T ∧ δ T < 1 / 2 ∧
      2 * Real.pi * δ T / α ≤ 1 ∧ 2 * Real.exp 3 * (2 * Real.pi * δ T / α) * Y T < 1 ∧
      ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → ∀ t ∈ Icc (α / 2 * T) (3 * α * T),
        ‖ratioForm (molLen θ T) a b t‖ ≤ CU * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
    have hδ' : Tendsto (fun T => 2 * Real.pi * δ T / α) atTop (𝓝 0) := by
      have := (hδ0.const_mul (2 * Real.pi)).div_const α
      simpa using this
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 * |β| / α),
      hδ0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hδ'.eventually (ge_mem_nhds one_pos), hunique.eventually (gt_mem_nhds one_pos), hU]
      with T h1 h2 h3 h4 h5 h6
    refine ⟨h1, ?_, h3, h4, h5, h6⟩
    rw [div_le_iff₀ hα] at h2; linarith
  -- positions on the progression
  have hrange : ∀ {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T → ∀ x : ℝ, ψ (x / T) ≠ 0 →
      α * x + β ∈ Icc (α / 2 * T) (3 * α * T) := by
    intro T hT hβ x hx
    have hT0 : 0 < T := by linarith
    obtain ⟨h1, h2⟩ := hsupp hx
    rw [le_div_iff₀ hT0] at h1
    rw [div_le_iff₀ hT0] at h2
    constructor
    · have := neg_abs_le β; nlinarith
    · have := le_abs_self β; nlinarith
  have hposT : ∀ {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T → ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β := by
    intro T hT hβ x hx
    have := (hrange hT hβ x hx).1
    have hT0 : 0 < T := by linarith
    have : 0 < α / 2 * T := by positivity
    linarith
  -- the summand and its fibres over `j = round u(c)`
  set g : ℝ → ℕ × ℕ → ℝ := fun T => (smallResonant α θ T).indicator
    (fun c => ‖fiberTerm ψ α β (molLen θ T) T c‖ / T)
  set jOf : ℕ × ℕ → ℤ := fun c => round (ratioPhase α c)
  set G : ℝ → ℤ → ℝ := fun T j => ∑' c : ↥(jOf ⁻¹' {j}), g T c
  -- properties of the support
  have hsupp_g : ∀ {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T → δ T < 1 / 2 → ∀ c : ℕ × ℕ, g T c ≠ 0 →
      0 < c.1 ∧ 0 < c.2 ∧ Nat.Coprime c.1 c.2 ∧ jOf c ≠ 0 ∧
        |ratioPhase α c - jOf c| < δ T ∧ ((c.1 * c.2 : ℕ) : ℝ) < Y T := by
    intro T hT hβ hδh c hc
    have hmem : c ∈ smallResonant α θ T := by
      by_contra h; exact hc (Set.indicator_of_notMem h _)
    obtain ⟨⟨j, hj0, hj⟩, hY⟩ := hmem
    have hround : jOf c = j := round_eq_of_abs_sub_lt (hj.trans hδh)
    have hΦ : fiberTerm ψ α β (molLen θ T) T c ≠ 0 := by
      intro h0; apply hc
      simp only [g, Set.indicator_of_mem (show c ∈ smallResonant α θ T from ⟨⟨j, hj0, hj⟩, hY⟩),
        h0, norm_zero, zero_div]
    have hcop : Nat.Coprime c.1 c.2 ∧ 0 < c.1 ∧ 0 < c.2 := by
      by_contra h; exact hΦ (fiberTerm_eq_zero h)
    exact ⟨hcop.2.1, hcop.2.2, hcop.1, by rw [hround]; exact hj0, by rw [hround]; exact hj, hY⟩
  -- the bound on each summand
  have hval : ∀ {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T →
      (∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → ∀ t ∈ Icc (α / 2 * T) (3 * α * T),
        ‖ratioForm (molLen θ T) a b t‖ ≤ CU * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ)) →
      ∀ c : ℕ × ℕ, 0 < c.1 → 0 < c.2 → Nat.Coprime c.1 c.2 →
        ‖fiberTerm ψ α β (molLen θ T) T c‖ / T ≤
          2 * Ψ₀ * CU * ((c.1 * c.2 : ℕ) : ℝ) ^ (-(1 / 6) : ℝ) := by
    intro T hT hβ hUT c ha hb hcop
    have hab0 : (0 : ℝ) < ((c.1 * c.2 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hb
    have h := fiberTerm_div_le hsupp hΨ (molLen θ T) hT (hposT hT hβ) hcop ha hb
      (M := CU * ((c.1 * c.2 : ℕ) : ℝ) ^ (1 / 3 : ℝ)) (by positivity)
      (fun x hx => hUT _ _ hcop ha hb _ (hrange hT hβ x hx))
    have e : (Real.sqrt ((c.1 : ℝ) * c.2))⁻¹ * (CU * ((c.1 * c.2 : ℕ) : ℝ) ^ (1 / 3 : ℝ)) =
        CU * ((c.1 * c.2 : ℕ) : ℝ) ^ (-(1 / 6) : ℝ) := by
      rw [← sqrt_inv_mul_rpow hab0]; push_cast; ring
    rw [e] at h
    calc ‖fiberTerm ψ α β (molLen θ T) T c‖ / T ≤ 2 * Ψ₀ * (CU * ((c.1 * c.2 : ℕ) : ℝ) ^ (-(1 / 6) : ℝ)) := by
          simpa using h
      _ = _ := by ring
  -- at most one ratio per `j`
  have hsub : ∀ {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T → δ T < 1 / 2 → 2 * Real.pi * δ T / α ≤ 1 →
      2 * Real.exp 3 * (2 * Real.pi * δ T / α) * Y T < 1 → ∀ j : ℤ,
      (Function.support (fun c : ↥(jOf ⁻¹' {j}) => g T c)).Subsingleton := by
    intro T hT hβ hδh hδ1 hun j x hx y hy
    have hxj : jOf x.1 = j := x.2
    have hyj : jOf y.1 = j := y.2
    obtain ⟨xa, xb, xcop, -, xph, xY⟩ := hsupp_g hT hβ hδh x.1 hx
    obtain ⟨ya, yb, ycop, -, yph, yY⟩ := hsupp_g hT hβ hδh y.1 hy
    rw [hxj] at xph
    rw [hyj] at yph
    have hxw : x.1 ∈ windowSet α (2 * Real.pi * δ T / α) (Y T) j :=
      mem_windowSet.mpr ⟨xa, xb, xcop, xY, abs_ratioLog_sub_lt hα xph⟩
    have hyw : y.1 ∈ windowSet α (2 * Real.pi * δ T / α) (Y T) j :=
      mem_windowSet.mpr ⟨ya, yb, ycop, yY, abs_ratioLog_sub_lt hα yph⟩
    have hcard := card_window_le (α := α) (by positivity) hδ1
      (by simp only [Y]; positivity : (0 : ℝ) ≤ Y T) j
    have hle1 : (windowSet α (2 * Real.pi * δ T / α) (Y T) j).card ≤ 1 := by
      have : ((windowSet α (2 * Real.pi * δ T / α) (Y T) j).card : ℝ) < 2 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    exact Subtype.ext (Finset.card_le_one.mp hle1 _ hxw _ hyw)
  -- summability and the fibre decomposition
  have hfib : ∀ᶠ T : ℝ in atTop, ∑' c, g T c = ∑' j, G T j := by
    filter_upwards [hgood] with T hTg
    obtain ⟨hT, hβ, -⟩ := hTg
    have hs := ((summable_norm_fiberTerm hsupp (molLen θ T) (by linarith)
      (hposT hT hβ)).div_const T).indicator (smallResonant α θ T)
    exact (hs.hasSum.tsum_fiberwise jOf).tsum_eq.symm
  -- the dominating bound
  set bnd : ℤ → ℝ := fun j =>
    2 * Ψ₀ * CU * Real.exp (1 / 6) * Real.exp (-(Real.pi / (3 * α)) * |(j : ℝ)|)
  have hbnd : Summable bnd := by
    have hr : Real.exp (-(Real.pi / (3 * α))) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < Real.pi / (3 * α) := by positivity
      linarith)
    have hg := (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (2 * Ψ₀ * CU * Real.exp (1 / 6))
    have hconv : ∀ n : ℕ, Real.exp (-(Real.pi / (3 * α))) ^ n =
        Real.exp (-(Real.pi / (3 * α)) * (n : ℝ)) := fun n => by
      rw [← Real.exp_nat_mul]; ring_nf
    refine Summable.of_nat_of_neg ?_ ?_
    · refine hg.congr fun n => ?_
      simp only [bnd, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), hconv]
    · refine hg.congr fun n => ?_
      simp only [bnd, Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), hconv]
  have hbnd0 : ∀ j, 0 ≤ bnd j := fun j => by simp only [bnd]; positivity
  have hG0 : ∀ {T : ℝ}, 0 ≤ T → ∀ j, 0 ≤ G T j := fun {T} hT j =>
    tsum_nonneg fun c => Set.indicator_nonneg (fun _ _ => div_nonneg (norm_nonneg _) hT) _
  -- the bound per term
  have hterm : ∀ {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T → δ T < 1 / 2 → 2 * Real.pi * δ T / α ≤ 1 →
      (∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → ∀ t ∈ Icc (α / 2 * T) (3 * α * T),
        ‖ratioForm (molLen θ T) a b t‖ ≤ CU * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ)) →
      ∀ j : ℤ, ∀ c : ↥(jOf ⁻¹' {j}), g T c ≤ bnd j := by
    intro T hT hβ hδh hδ1 hUT j c
    by_cases hc : g T c = 0
    · rw [hc]; exact hbnd0 j
    obtain ⟨ha, hb, hcop, -, hph, -⟩ := hsupp_g hT hβ hδh c.1 hc
    have hcj : jOf c.1 = j := c.2
    rw [hcj] at hph
    have hmem : c.1 ∈ smallResonant α θ T := by
      by_contra h; exact hc (Set.indicator_of_notMem h _)
    simp only [g, Set.indicator_of_mem hmem]
    refine (hval hT hβ hUT c.1 ha hb hcop).trans ?_
    have hexp := exp_le_of_resonant hα ha hb (abs_ratioLog_sub_lt hα hph)
    have h6 := rpow_neg_sixth_le hexp
    have hL : Real.exp (-((2 * Real.pi * |(j : ℝ)| / α - 2 * Real.pi * δ T / α) / 6)) ≤
        Real.exp (1 / 6) * Real.exp (-(Real.pi / (3 * α)) * |(j : ℝ)|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : 2 * Real.pi * |(j : ℝ)| / α / 6 = Real.pi / (3 * α) * |(j : ℝ)| := by
        field_simp; ring
      nlinarith
    calc 2 * Ψ₀ * CU * ((c.1.1 * c.1.2 : ℕ) : ℝ) ^ (-(1 / 6) : ℝ)
        ≤ 2 * Ψ₀ * CU * (Real.exp (1 / 6) * Real.exp (-(Real.pi / (3 * α)) * |(j : ℝ)|)) := by
          gcongr; exact h6.trans hL
      _ = bnd j := by simp only [bnd]; ring
  have hdom : ∀ᶠ T : ℝ in atTop, ∀ j, ‖G T j‖ ≤ bnd j := by
    filter_upwards [hgood] with T hTg j
    obtain ⟨hT, hβ, hδh, hδ1, hun, hUT⟩ := hTg
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 (by linarith) j)]
    exact tsum_le_of_subsingleton_support (hsub hT hβ hδh hδ1 hun j) (hbnd0 j)
      (hterm hT hβ hδh hδ1 hUT j)
  -- pointwise limits
  have hlim : ∀ j, Tendsto (fun T => G T j) atTop (𝓝 0) := by
    intro j
    by_cases hj : j = 0
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hgood] with T hTg
      obtain ⟨hT, hβ, hδh, -⟩ := hTg
      symm
      refine (tsum_congr fun c => ?_).trans tsum_zero
      by_contra hc
      obtain ⟨-, -, -, hj0, -⟩ := hsupp_g hT hβ hδh c.1 hc
      exact hj0 (c.2.trans hj)
    rw [Metric.tendsto_nhds]
    intro ε hε
    set K₀ : ℝ := 2 * Ψ₀ * CU + 1
    have hK₀ : 0 < K₀ := by positivity
    set X₀ : ℝ := (4 * K₀ / ε) ^ 6 + 1
    have hX₀' : 0 ≤ (4 * K₀ / ε) ^ 6 := by positivity
    have hX₀ : 1 ≤ X₀ := by linarith
    set ε₁ : ℝ := ε / (4 * Ψ₀ + 4)
    have hε₁ : 0 < ε₁ := by positivity
    set Fin : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊X₀⌋₊ ×ˢ Finset.Icc 1 ⌊X₀⌋₊).filter
      fun c => Nat.Coprime c.1 c.2
    have hfin : ∀ c ∈ Fin, ∀ᶠ T : ℝ in atTop,
        (ratioPhase α c = j → ∀ t ∈ Icc (α / 2 * T) (3 * α * T),
          ‖ratioForm (molLen θ T) c.1 c.2 t‖ ≤ ε₁) ∧
        (ratioPhase α c ≠ j → δ T < |ratioPhase α c - j|) := by
      intro c hc
      obtain ⟨hcI, hcop⟩ := Finset.mem_filter.mp hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hcI
      have ha := (Finset.mem_Icc.mp hc1).1
      have hb := (Finset.mem_Icc.mp hc2).1
      by_cases hph : ratioPhase α c = j
      · have hne : 1 < c.1 ∨ 1 < c.2 := by
          by_contra h
          push Not at h
          have h1 : c.1 = 1 := by omega
          have h2 : c.2 = 1 := by omega
          apply hj
          have : ratioPhase α c = 0 := by
            unfold ratioPhase; rw [h1, h2]; simp
          exact_mod_cast hph.symm.trans this
        filter_upwards [ratioForm_uniform_of_ne hθ0 hθ (c₁ := α / 2) (c₂ := 3 * α) (by positivity)
          (by linarith) hcop ha hb hne hε₁] with T hT
        exact ⟨fun _ => hT, fun h => absurd hph h⟩
      · have hd : 0 < |ratioPhase α c - j| := abs_pos.mpr (sub_ne_zero.mpr hph)
        filter_upwards [hδ0.eventually (gt_mem_nhds hd)] with T hT
        exact ⟨fun h => absurd h hph, fun _ => hT⟩
    filter_upwards [hgood, (Filter.eventually_all_finset Fin).mpr hfin] with T hTg hF
    obtain ⟨hT, hβ, hδh, hδ1, hun, hUT⟩ := hTg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hG0 (by linarith) j)]
    refine lt_of_le_of_lt (tsum_le_of_subsingleton_support (hsub hT hβ hδh hδ1 hun j)
      (by positivity : (0 : ℝ) ≤ ε / 2) fun c => ?_) (by linarith)
    by_cases hc : g T c = 0
    · rw [hc]; positivity
    obtain ⟨ha, hb, hcop, -, hph, -⟩ := hsupp_g hT hβ hδh c.1 hc
    have hcj : jOf c.1 = j := c.2
    rw [hcj] at hph
    have hmem : c.1 ∈ smallResonant α θ T := by
      by_contra h; exact hc (Set.indicator_of_notMem h _)
    simp only [g, Set.indicator_of_mem hmem]
    by_cases hsmall : c.1.1 ≤ ⌊X₀⌋₊ ∧ c.1.2 ≤ ⌊X₀⌋₊
    · have hcF : c.1 ∈ Fin := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, hsmall.1⟩,
          Finset.mem_Icc.mpr ⟨hb, hsmall.2⟩⟩, hcop⟩
      obtain ⟨hex, hnex⟩ := hF c.1 hcF
      have hphj : ratioPhase α c.1 = j := by
        by_contra h; exact absurd hph (not_lt.mpr (hnex h).le)
      have hb' := fiberTerm_div_le hsupp hΨ (molLen θ T) hT (hposT hT hβ) hcop ha hb hε₁.le
        (fun x hx => hex hphj _ (hrange hT hβ x hx))
      have hsq : (Real.sqrt ((c.1.1 : ℝ) * c.1.2))⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        rw [Real.one_le_sqrt]
        have : (1 : ℝ) ≤ c.1.1 := by exact_mod_cast ha
        have : (1 : ℝ) ≤ c.1.2 := by exact_mod_cast hb
        nlinarith
      calc ‖fiberTerm ψ α β (molLen θ T) T c.1‖ / T
          ≤ 2 * Ψ₀ * ((Real.sqrt ((c.1.1 : ℝ) * c.1.2))⁻¹ * ε₁) := by simpa using hb'
        _ ≤ 2 * Ψ₀ * (1 * ε₁) := by gcongr
        _ ≤ ε / 2 := by
            simp only [ε₁, one_mul]
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    · have hbig : X₀ ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) := by
        push Not at hsmall
        have h1 : (1 : ℝ) ≤ c.1.1 := by exact_mod_cast ha
        have h2 : (1 : ℝ) ≤ c.1.2 := by exact_mod_cast hb
        push_cast
        by_cases h : c.1.1 ≤ ⌊X₀⌋₊
        · have := Nat.floor_lt (by linarith) |>.mp (hsmall h)
          nlinarith
        · have := Nat.floor_lt (by linarith) |>.mp (not_le.mp h)
          nlinarith
      refine (hval hT hβ hUT c.1 ha hb hcop).trans ?_
      have hX : X₀ ^ (-(1 / 6) : ℝ) ≤ ε / (4 * K₀) := by
        calc X₀ ^ (-(1 / 6) : ℝ) ≤ ((4 * K₀ / ε) ^ 6) ^ (-(1 / 6) : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
          _ = ε / (4 * K₀) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
              norm_num
              rw [Real.rpow_neg_one, inv_div]
      calc 2 * Ψ₀ * CU * ((c.1.1 * c.1.2 : ℕ) : ℝ) ^ (-(1 / 6) : ℝ)
          ≤ 2 * Ψ₀ * CU * X₀ ^ (-(1 / 6) : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hbig
              (by norm_num)) (by positivity)
        _ ≤ 2 * Ψ₀ * CU * (ε / (4 * K₀)) := by gcongr
        _ ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
  have h := tendsto_tsum_of_dominated_convergence hbnd hlim hdom
  simp only [tsum_zero] at h
  exact h.congr' (by filter_upwards [hfib] with T hT; exact hT.symm)

end

end RHTower.VerticalAP
