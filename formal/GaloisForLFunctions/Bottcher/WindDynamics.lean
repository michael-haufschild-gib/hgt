/-
# Winding of a composed loop, and its dynamical algebra

For a nowhere-zero continuous `g : X → ℂ` and a loop `p` at `x₀`, the **transported loop**
`t ↦ g(p t)/g(x₀)` is a loop in `ℂ*` based at `1`; its degree `wind g p := deg⟦·⟧` is the winding
number of `g ∘ p` around `0`. Because we divide by the basepoint, everything lives at the single
basepoint `1`, so the whole `Pi1CMinusZero` calculus applies verbatim. The resulting algebra —

* `wind_mul`   : `wind (g·h) = wind g + wind h`        (pointwise product; `degZ_mulLoop`)
* `wind_pow`   : `wind (gᵏ)   = k · wind g`            (`degZ_powLoop`)
* `wind_const` : `wind (const) = 0`
* `wind_zero_of_re_pos` : a factor staying in the right half-plane is windingless (`degZ_zero_of_re_pos`)
* `wind_exp`   : `wind (exp ∘ M) = 0`                  (lifts to `M ∘ p`, a closed loop)

— is exactly the bookkeeping that turns "f is degree 2" into "the winding of `βlev_n ∘ f` is even":
`f ∘ g = g² · (1 + c/g²)`, and the corrector `1 + c/g²` stays near `1`. -/
import GaloisForLFunctions.Bottcher.Pi1CMinusZero

open Topology unitInterval
open Pi1CMinusZero

namespace Bottcher

variable {X : Type*} [TopologicalSpace X]

/-- The transported loop `t ↦ g(p t)/g(x₀)`, a loop in `ℂ*` based at `1`. -/
noncomputable def transLoop (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) : Path one_cs one_cs where
  toFun := fun t => ⟨g (p t) / g x₀, div_ne_zero (hgne _) (hgne _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((hg.comp p.continuous_toFun).div_const _)
  source' := by
    apply Subtype.ext
    show g (p 0) / g x₀ = (1 : ℂ); rw [p.source]; exact div_self (hgne _)
  target' := by
    apply Subtype.ext
    show g (p 1) / g x₀ = (1 : ℂ); rw [p.target]; exact div_self (hgne _)

/-- The winding number of `g ∘ p` around `0`. -/
noncomputable def wind (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) : ℤ :=
  degZ ⟦transLoop g hg hgne p⟧

/-- Pointwise value of a power loop. -/
theorem powLoop_apply (k : ℕ) (q : Path one_cs one_cs) (t : I) :
    ((powLoop k q) t : ℂ) = (q t : ℂ) ^ k := by
  induction k with
  | zero => show ((Path.refl one_cs) t : ℂ) = (q t : ℂ) ^ (0 : ℕ); rw [pow_zero]; rfl
  | succ k ih =>
    show ((mulLoop q (powLoop k q)) t : ℂ) = (q t : ℂ) ^ (k + 1)
    show (q t : ℂ) * ((powLoop k q) t : ℂ) = (q t : ℂ) ^ (k + 1)
    rw [ih, pow_succ]; ring

/-- **Winding is additive under pointwise products.** -/
theorem wind_mul (g h : X → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hgne : ∀ x, g x ≠ 0) (hhne : ∀ x, h x ≠ 0) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => g x * h x) (hg.mul hh) (fun x => mul_ne_zero (hgne x) (hhne x)) p
      = wind g hg hgne p + wind h hh hhne p := by
  have hpath : transLoop (fun x => g x * h x) (hg.mul hh)
      (fun x => mul_ne_zero (hgne x) (hhne x)) p
      = mulLoop (transLoop g hg hgne p) (transLoop h hh hhne p) := by
    apply Path.ext; funext t; apply Subtype.ext
    show g (p t) * h (p t) / (g x₀ * h x₀) = g (p t) / g x₀ * (h (p t) / h x₀)
    rw [div_mul_div_comm]
  simp only [wind]
  rw [hpath, degZ_mulLoop]

/-- A constant loop has winding `0`. -/
theorem wind_const (a : ℂ) (ha : a ≠ 0) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun _ => a) continuous_const (fun _ => ha) p = 0 := by
  have hpath : transLoop (fun _ => a) continuous_const (fun _ => ha) p = Path.refl one_cs := by
    apply Path.ext; funext t; apply Subtype.ext
    show a / a = (1 : ℂ); exact div_self ha
  show degZ ⟦transLoop (fun _ => a) _ _ p⟧ = 0
  rw [hpath, degZ_refl]

/-- **Winding of a pointwise power:** `wind (gᵏ) = k · wind g`. -/
theorem wind_pow (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    (k : ℕ) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => g x ^ k) (hg.pow k) (fun x => pow_ne_zero k (hgne x)) p
      = k * wind g hg hgne p := by
  have hpath : transLoop (fun x => g x ^ k) (hg.pow k) (fun x => pow_ne_zero k (hgne x)) p
      = powLoop k (transLoop g hg hgne p) := by
    apply Path.ext; funext t; apply Subtype.ext
    show g (p t) ^ k / g x₀ ^ k = ((powLoop k (transLoop g hg hgne p)) t : ℂ)
    rw [powLoop_apply, ← div_pow]; rfl
  simp only [wind]
  rw [hpath, degZ_powLoop]

/-- A factor whose transported loop stays in the right half-plane is windingless. -/
theorem wind_zero_of_re_pos (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) (hre : ∀ t : I, 0 < (g (p t) / g x₀).re) :
    wind g hg hgne p = 0 :=
  degZ_zero_of_re_pos _ (fun t => hre t)

/-- **`wind (exp ∘ M) = 0`** for any continuous `M`: the transported loop `exp(M∘p − M(x₀))` lifts to
the closed loop `M ∘ p − M(x₀)`, whose endpoints coincide. -/
theorem wind_exp (M : X → ℂ) (hM : Continuous M) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => Complex.exp (M x)) (Complex.continuous_exp.comp hM)
      (fun x => Complex.exp_ne_zero (M x)) p = 0 := by
  set q : Path one_cs one_cs :=
    transLoop (fun x => Complex.exp (M x)) (Complex.continuous_exp.comp hM)
      (fun x => Complex.exp_ne_zero (M x)) p with hq
  set L : C(I, ℂ) := ⟨fun t => M (p t) - M x₀, by fun_prop⟩ with hLdef
  have hL : pexp ∘ L = q := by
    funext t; apply Subtype.ext
    show Complex.exp (M (p t) - M x₀) = Complex.exp (M (p t)) / Complex.exp (M x₀)
    rw [Complex.exp_sub]
  have h0 : L 0 = (e0 : ℂ) := by
    show M (p 0) - M x₀ = (e0 : ℂ); rw [p.source]; show M x₀ - M x₀ = (0 : ℂ); ring
  have hc : (degClass ⟦q⟧ : ℂ) = L 1 := degClass_eq_of_lift q L hL h0
  have h1 : (L : I → ℂ) 1 = 0 := by
    show M (p 1) - M x₀ = (0 : ℂ); rw [p.target]; ring
  rw [h1] at hc
  show degZ ⟦q⟧ = 0
  have hsp := degOfFiber_spec (degClass ⟦q⟧)
  have hzero : (degOfFiber (degClass ⟦q⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 :=
    hsp.symm.trans hc
  have hz : (degOfFiber (degClass ⟦q⟧) : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right twopiI_ne_zero
  show fiberEquivInt _ = 0
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hz

/-- `wind` depends only on the function (the continuity / nonvanishing data are `Prop`). -/
theorem wind_congr {g₁ g₂ : X → ℂ} (h : g₁ = g₂)
    (hg₁ : Continuous g₁) (hg₁ne : ∀ x, g₁ x ≠ 0)
    (hg₂ : Continuous g₂) (hg₂ne : ∀ x, g₂ x ≠ 0) {x₀ : X} (p : Path x₀ x₀) :
    wind g₁ hg₁ hg₁ne p = wind g₂ hg₂ hg₂ne p := by
  subst h; rfl

/-- **A factor whose raw values stay in the slit plane is windingless** (e.g. all in `{Re > 0}`).
The lift is `log(g∘p) − log(g x₀)`, a closed loop. -/
theorem wind_zero_of_slitPlane (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) (hslit : ∀ t : I, g (p t) ∈ Complex.slitPlane) :
    wind g hg hgne p = 0 := by
  set q : Path one_cs one_cs := transLoop g hg hgne p with hq
  have hcont : Continuous fun t : I => Complex.log (g (p t)) - Complex.log (g x₀) :=
    ((hg.comp p.continuous_toFun).clog hslit).sub continuous_const
  set L : C(I, ℂ) := ⟨fun t => Complex.log (g (p t)) - Complex.log (g x₀), hcont⟩ with hLdef
  have hL : pexp ∘ L = q := by
    funext t; apply Subtype.ext
    show Complex.exp (Complex.log (g (p t)) - Complex.log (g x₀)) = g (p t) / g x₀
    rw [Complex.exp_sub, Complex.exp_log (hgne _), Complex.exp_log (hgne _)]
  have h0 : L 0 = (e0 : ℂ) := by
    show Complex.log (g (p 0)) - Complex.log (g x₀) = (e0 : ℂ); rw [p.source]; show _ - _ = (0:ℂ); ring
  have h1 : (L : I → ℂ) 1 = 0 := by
    show Complex.log (g (p 1)) - Complex.log (g x₀) = (0 : ℂ); rw [p.target]; ring
  have hc : (degClass ⟦q⟧ : ℂ) = L 1 := degClass_eq_of_lift q L hL h0
  rw [h1] at hc
  show degZ ⟦q⟧ = 0
  have hsp := degOfFiber_spec (degClass ⟦q⟧)
  have hzero : (degOfFiber (degClass ⟦q⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 :=
    hsp.symm.trans hc
  have hz : (degOfFiber (degClass ⟦q⟧) : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right twopiI_ne_zero
  show fiberEquivInt _ = 0
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hz

/-- **The dynamical doubling.** For `g` with `‖c‖ < ‖g‖²` everywhere (so `f∘g = g²+c` stays large and
the corrector `1 + c/g²` stays near `1`), the winding doubles: `wind(g²+c) = 2·wind(g)`. This is
"`f = z²+c` is degree 2" expressed as a winding identity. -/
theorem wind_quadratic (c : ℂ) (g : X → ℂ) (hg : Continuous g)
    (hgbig : ∀ x, ‖c‖ < ‖g x‖ ^ (2 : ℕ)) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => g x ^ (2 : ℕ) + c) (by fun_prop)
        (fun x => by
          show g x ^ (2 : ℕ) + c ≠ 0
          have h := hgbig x
          have hpos : (0 : ℝ) < ‖g x ^ (2 : ℕ) + c‖ := by
            have hle : ‖g x‖ ^ (2 : ℕ) - ‖c‖ ≤ ‖g x ^ (2 : ℕ) + c‖ := by
              have := norm_sub_norm_le (g x ^ (2 : ℕ)) (-c)
              simpa [norm_pow, norm_neg, sub_neg_eq_add] using this
            linarith
          intro hz; rw [hz, norm_zero] at hpos; exact lt_irrefl 0 hpos) p
      = 2 * wind g hg (fun x => by
          have h := hgbig x
          have hp : (0 : ℝ) < ‖g x‖ ^ (2 : ℕ) := lt_of_le_of_lt (norm_nonneg c) h
          intro hgx; rw [hgx, norm_zero] at hp; norm_num at hp) p := by
  have gne : ∀ x, g x ≠ 0 := fun x => by
    have h := hgbig x
    have hp : (0 : ℝ) < ‖g x‖ ^ (2 : ℕ) := lt_of_le_of_lt (norm_nonneg c) h
    intro hgx; rw [hgx, norm_zero] at hp; norm_num at hp
  -- corrector `B x = 1 + c / g x²`
  set B : X → ℂ := fun x => 1 + c / g x ^ (2 : ℕ) with hB
  have hg2ne : ∀ x, g x ^ (2 : ℕ) ≠ 0 := fun x => pow_ne_zero 2 (gne x)
  -- `B x` stays near `1`: `‖c / g x²‖ < 1`
  have hBsmall : ∀ x, ‖c / g x ^ (2 : ℕ)‖ < 1 := fun x => by
    have hpos : (0 : ℝ) < ‖g x‖ ^ (2 : ℕ) := lt_of_le_of_lt (norm_nonneg c) (hgbig x)
    rw [norm_div, norm_pow, div_lt_one hpos]
    exact hgbig x
  have hBne : ∀ x, B x ≠ 0 := fun x => by
    have hb := hBsmall x
    intro h0
    have hcg : c / g x ^ (2 : ℕ) = -1 := by
      have h1 : (1 : ℂ) + c / g x ^ (2 : ℕ) = 0 := h0
      linear_combination h1
    rw [hcg] at hb; simp at hb
  have hBcont : Continuous B := by fun_prop (disch := exact hg2ne _)
  -- factorisation `g² + c = g² · B`
  have hfun : (fun x => g x ^ (2 : ℕ) + c) = (fun x => g x ^ (2 : ℕ) * B x) := by
    funext x
    show g x ^ (2 : ℕ) + c = g x ^ (2 : ℕ) * (1 + c / g x ^ (2 : ℕ))
    rw [mul_add, mul_one, mul_div_cancel₀ c (hg2ne x)]
  rw [wind_congr hfun (by fun_prop) _ (by fun_prop (disch := exact hg2ne _)) _ p]
  · rw [wind_mul (fun x => g x ^ (2 : ℕ)) B (by fun_prop) hBcont hg2ne hBne p]
    rw [wind_pow g hg gne 2 p]
    -- corrector is windingless: `Re (B (p t)) > 0`
    have hBslit : ∀ t : I, B (p t) ∈ Complex.slitPlane := fun t => by
      refine Or.inl ?_
      show 0 < (1 + c / g (p t) ^ (2 : ℕ)).re
      have hb := hBsmall (p t)
      have habs : |(c / g (p t) ^ (2 : ℕ)).re| < 1 :=
        lt_of_le_of_lt (Complex.abs_re_le_norm _) hb
      have hlow := (abs_lt.mp habs).1
      simp only [Complex.add_re, Complex.one_re]
      linarith
    rw [wind_zero_of_slitPlane B hBcont hBne p hBslit]
    push_cast; ring
  · exact fun x => mul_ne_zero (hg2ne x) (hBne x)

/-- **The halving step.** If `G^(2ⁿ) = H` and `H` has winding divisible by `2ⁿ⁺¹`, then `G` has
*even* winding `2m`. Instantiated with `G = βlev_n ∘ f` and `H = bottcherCoord ∘ f^[n+1]` (whose
winding is `2ⁿ⁺¹ · wind(id)` by the iterate-doubling), this is exactly the evenness that discharges
`hlift`. -/
theorem wind_even_of_pow (n : ℕ) (G H : X → ℂ) (hG : Continuous G) (hGne : ∀ x, G x ≠ 0)
    (hH : Continuous H) (hHne : ∀ x, H x ≠ 0) {x₀ : X} (p : Path x₀ x₀) (m : ℤ)
    (hpow : ∀ x, G x ^ (2 ^ n) = H x)
    (hwindH : wind H hH hHne p = 2 ^ (n + 1) * m) :
    wind G hG hGne p = 2 * m := by
  have hfun : (fun x => G x ^ (2 ^ n)) = H := funext hpow
  have h1 : wind (fun x => G x ^ (2 ^ n)) (hG.pow _) (fun x => pow_ne_zero _ (hGne x)) p
      = wind H hH hHne p :=
    wind_congr hfun (hG.pow _) (fun x => pow_ne_zero _ (hGne x)) hH hHne p
  rw [wind_pow G hG hGne (2 ^ n) p, hwindH] at h1
  push_cast at h1
  have h2 : (2 : ℤ) ^ n * wind G hG hGne p = (2 : ℤ) ^ n * (2 * m) := by
    rw [h1, pow_succ]; ring
  exact mul_left_cancel₀ (pow_ne_zero n (two_ne_zero)) h2

/-! ## From normalized winding to the square-lift criterion -/

/-- Normalize a nowhere-zero continuous map to have value `1` at the basepoint. -/
noncomputable def normalizeToOne {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) (x₀ : X) : C(X, Cs) where
  toFun := fun x => ⟨(g x : ℂ) / (g x₀ : ℂ), div_ne_zero (g x).2 (g x₀).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp g.continuous).div_const _

@[simp] theorem normalizeToOne_base {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) (x₀ : X) : normalizeToOne g x₀ x₀ = one_cs := by
  apply Subtype.ext
  show (g x₀ : ℂ) / (g x₀ : ℂ) = (1 : ℂ)
  exact div_self (g x₀).2

/-- The path induced by the normalized map is exactly the transported loop used by `wind`. -/
theorem normalizeToOne_path_eq_transLoop {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) {x₀ : X} (p : Path x₀ x₀) :
    ((p.map (normalizeToOne g x₀).continuous).cast
        (normalizeToOne_base g x₀).symm (normalizeToOne_base g x₀).symm)
      = transLoop (fun x => (g x : ℂ)) (continuous_subtype_val.comp g.continuous)
          (fun x => (g x).2) p := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/-- **Even normalized winding gives the square-lift `π₁` condition.** If every normalized loop of a
nowhere-zero map `g` has even `degZ`, then the normalized map's induced fundamental-group image lies in
the image of the square map. This is the bridge from the project's winding calculus to Mathlib's
covering-space lifting hypothesis. -/
theorem normalized_square_range_of_even_winding {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) {x₀ : X}
    (hwind : ∀ p : Path x₀ x₀,
      Even (degZ ⟦transLoop (fun x => (g x : ℂ)) (continuous_subtype_val.comp g.continuous)
          (fun x => (g x).2) p⟧)) :
    (FundamentalGroup.mapOfEq (normalizeToOne g x₀) (normalizeToOne_base g x₀)).range ≤
      (FundamentalGroup.mapOfEq ⟨sqCs, continuous_sqCs⟩ sqCs_one).range := by
  intro γ hγ
  rcases hγ with ⟨δ, rfl⟩
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath δ)
  have hδ : δ = FundamentalGroup.fromPath (.mk p) := hp.symm
  subst δ
  apply Pi1CMinusZero.mem_sq_range_of_even_deg
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, normalizeToOne_path_eq_transLoop]
  exact hwind p

/-- Multiplying a transported loop by its basepoint recovers the original image loop, allowing a
different but equal basepoint `b` for dependent casts. -/
theorem map_mulBase_transLoop_eq_of_base {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) {x₀ : X} (p : Path x₀ x₀) {b : Cs} (hb : b = g x₀) :
    ((transLoop (fun x => (g x : ℂ)) (continuous_subtype_val.comp g.continuous)
          (fun x => (g x).2) p).map (mulBaseMap b).continuous).cast
        (mulBaseMap_one b).symm (mulBaseMap_one b).symm =
      (p.map g.continuous).cast hb hb := by
  subst hb
  apply Path.ext
  funext t
  apply Subtype.ext
  show (g x₀ : ℂ) * ((g (p t) : ℂ) / (g x₀ : ℂ)) = (g (p t) : ℂ)
  exact mul_div_cancel₀ (g (p t) : ℂ) (g x₀).2

/-- **Even transported winding gives the exact square-cover lift condition.** This is the non-normalized
form consumed by `CoveringRoot`: if `e₀² = g x₀` and every loop transported by `g` has even degree, then
`g_*π₁` lies in the image of the square map based at `e₀`. -/
theorem square_range_of_even_winding {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) {x₀ : X} {e₀ : Cs}
    (he : sqCs e₀ = g x₀)
    (hwind : ∀ p : Path x₀ x₀,
      Even (degZ ⟦transLoop (fun x => (g x : ℂ)) (continuous_subtype_val.comp g.continuous)
          (fun x => (g x).2) p⟧)) :
    (FundamentalGroup.map g x₀).range ≤
      (FundamentalGroup.mapOfEq ⟨sqCs, continuous_sqCs⟩ he).range := by
  intro γ hγ
  rcases hγ with ⟨δ, rfl⟩
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath δ)
  have hδ : δ = FundamentalGroup.fromPath (.mk p) := hp.symm
  subst δ
  rw [FundamentalGroup.map_apply]
  obtain ⟨q, hq⟩ := (degZ_even_iff_sq ⟦transLoop (fun x => (g x : ℂ))
      (continuous_subtype_val.comp g.continuous) (fun x => (g x).2) p⟧).mp (hwind p)
  refine ⟨FundamentalGroup.fromPath (.mk (scaleLoop e₀ q)), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  have hmapped := congrArg (fun Q : Path.Homotopic.Quotient one_cs one_cs =>
    Path.Homotopic.Quotient.map Q (mulBaseMap (sqCs e₀))) hq
  change ⟦(transLoop (fun x => (g x : ℂ)) (continuous_subtype_val.comp g.continuous)
      (fun x => (g x).2) p).map (mulBaseMap (sqCs e₀)).continuous⟧ =
    ⟦(sqLoop q).map (mulBaseMap (sqCs e₀)).continuous⟧ at hmapped
  have hhom := Path.Homotopic.Quotient.eq.mp hmapped
  have hhomCast := Path.Homotopic.pathCast hhom (mulBaseMap_one (sqCs e₀)).symm
    (mulBaseMap_one (sqCs e₀)).symm
  rw [map_mulBase_transLoop_eq_of_base g p he] at hhomCast
  rw [map_mulBase_sqLoop_eq_scaled_sq e₀ q] at hhomCast
  have hfinal := Path.Homotopic.pathCast hhomCast he.symm he.symm
  apply Quotient.sound
  simpa using! hfinal.symm

end Bottcher
