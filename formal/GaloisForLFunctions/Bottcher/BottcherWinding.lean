/-
# `bottcherCoord` preserves winding on `escapeOpen`

On `escapeOpen c` the Böttcher coordinate factors as `bottcherCoord c z = z · exp(S(z))` with
`S(z) = ∑ₖ bottcherLogTerm c z k` analytic (`bottcherCoord_eq_mul_exp`,
`differentiableOn_bottcherLogSum`). The `exp(S)` factor is windingless (`wind_exp`), so the winding of
`bottcherCoord c ∘ γ` around `0` equals the winding of the identity `z ↦ z` along `γ`, for every loop
`γ` in `escapeOpen c`. This is the bridge that lets winding around the puncture be read off the bare
position loop — the key step in identifying the `2ⁿ`-fold monodromy of the escape-level tower.
-/
import GaloisForLFunctions.Bottcher.WindDynamics
import GaloisForLFunctions.Bottcher.BasinColimit

open Topology unitInterval

namespace Bottcher

/-- Points of the far-field escape set are nonzero. -/
theorem escapeOpen_coe_ne_zero (c : ℂ) (z : escapeOpen c) : (z : ℂ) ≠ 0 := by
  refine norm_pos_iff.mp ?_
  exact lt_of_le_of_lt (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left 2 ‖c‖)) z.2

/-- Points of the far-field escape set satisfy the size hypothesis needed by `wind_quadratic`. -/
theorem escapeOpen_norm_c_lt_norm_sq (c : ℂ) (z : escapeOpen c) : ‖c‖ < ‖(z : ℂ)‖ ^ (2 : ℕ) := by
  have hc_lt : ‖c‖ < ‖(z : ℂ)‖ :=
    lt_of_le_of_lt (le_max_right 2 ‖c‖) z.2
  have htwo_lt : (2 : ℝ) < ‖(z : ℂ)‖ :=
    lt_of_le_of_lt (le_max_left 2 ‖c‖) z.2
  have hone_lt : (1 : ℝ) < ‖(z : ℂ)‖ := lt_trans (by norm_num) htwo_lt
  nlinarith [hc_lt, hone_lt]

/-- **`bottcherCoord` preserves winding on `escapeOpen`.** For any loop `p` in `escapeOpen c`, the
winding of `bottcherCoord c` along `p` equals the winding of the position map `z ↦ z` along `p`:
the `exp(S)` factor contributes nothing. -/
theorem wind_bottcherCoord_eq_wind_id (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀)
    (hgB : Continuous (fun x : escapeOpen c => bottcherCoord c (x : ℂ)))
    (hgBne : ∀ x : escapeOpen c, bottcherCoord c (x : ℂ) ≠ 0)
    (hgId : Continuous (fun x : escapeOpen c => (x : ℂ)))
    (hgIdne : ∀ x : escapeOpen c, (x : ℂ) ≠ 0) :
    wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne p
      = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne p := by
  set M : escapeOpen c → ℂ := fun x => ∑' k, bottcherLogTerm c (x : ℂ) k with hMdef
  have hM : Continuous M := (differentiableOn_bottcherLogSum c).continuousOn.restrict
  have hrel : (fun x : escapeOpen c => bottcherCoord c (x : ℂ))
      = (fun x : escapeOpen c => (x : ℂ) * Complex.exp (M x)) := by
    funext x; exact bottcherCoord_eq_mul_exp (hgIdne x)
  have key : wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne p
      = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne p
        + wind (fun x : escapeOpen c => Complex.exp (M x))
            (Complex.continuous_exp.comp hM) (fun x => Complex.exp_ne_zero _) p := by
    rw [wind_congr hrel hgB hgBne (hgId.mul (Complex.continuous_exp.comp hM))
      (fun x => mul_ne_zero (hgIdne x) (Complex.exp_ne_zero _)) p]
    exact wind_mul (fun x : escapeOpen c => (x : ℂ)) (fun x => Complex.exp (M x))
      hgId (Complex.continuous_exp.comp hM) hgIdne (fun x => Complex.exp_ne_zero _) p
  rw [key, wind_exp M hM, add_zero]

/-- **Functorial Böttcher winding bridge.** If a loop is first mapped continuously into the far-field
escape set, then applying `bottcherCoord` does not change its winding. This is the form needed on
escape-level subtypes: the remaining winding problem becomes the pure winding of the iterate image loop
in `escapeOpen`, with the `bottcherCoord = z · exp(S)` factor removed. -/
theorem wind_bottcherCoord_comp_eq_wind_coe (c : ℂ) {X : Type*} [TopologicalSpace X]
    (F : C(X, escapeOpen c)) {x₀ : X} (p : Path x₀ x₀)
    (hgB : Continuous (fun x : X => bottcherCoord c (F x : ℂ))) :
    wind (fun x : X => bottcherCoord c (F x : ℂ)) hgB (fun _ => bottcherCoord_ne_zero c _) p
      = wind (fun x : X => (F x : ℂ)) (continuous_subtype_val.comp F.continuous)
          (fun x => escapeOpen_coe_ne_zero c (F x)) p := by
  set M : escapeOpen c → ℂ := fun x => ∑' k, bottcherLogTerm c (x : ℂ) k with hMdef
  have hMesc : Continuous M := (differentiableOn_bottcherLogSum c).continuousOn.restrict
  have hM : Continuous fun x : X => M (F x) := hMesc.comp F.continuous
  have hrel : (fun x : X => bottcherCoord c (F x : ℂ))
      = (fun x : X => (F x : ℂ) * Complex.exp (M (F x))) := by
    funext x
    exact bottcherCoord_eq_mul_exp (escapeOpen_coe_ne_zero c (F x))
  have key :
      wind (fun x : X => bottcherCoord c (F x : ℂ)) hgB (fun _ => bottcherCoord_ne_zero c _) p
        = wind (fun x : X => (F x : ℂ)) (continuous_subtype_val.comp F.continuous)
            (fun x => escapeOpen_coe_ne_zero c (F x)) p
          + wind (fun x : X => Complex.exp (M (F x))) (Complex.continuous_exp.comp hM)
              (fun x => Complex.exp_ne_zero _) p := by
    rw [wind_congr hrel hgB (fun _ => bottcherCoord_ne_zero c _)
      ((continuous_subtype_val.comp F.continuous).mul (Complex.continuous_exp.comp hM))
      (fun x => mul_ne_zero (escapeOpen_coe_ne_zero c (F x)) (Complex.exp_ne_zero _)) p]
    exact wind_mul (fun x : X => (F x : ℂ)) (fun x => Complex.exp (M (F x)))
      (continuous_subtype_val.comp F.continuous) (Complex.continuous_exp.comp hM)
      (fun x => escapeOpen_coe_ne_zero c (F x)) (fun x => Complex.exp_ne_zero _) p
  rw [key, wind_exp (fun x : X => M (F x)) hM, add_zero]

/-- **Far-field degree two.** On `escapeOpen c`, the quadratic map doubles position winding. This is
the topological degree-two input in the region where the Böttcher coordinate is already defined. -/
theorem wind_quadratic_escapeOpen (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    wind (fun x : escapeOpen c => quadratic c (x : ℂ))
        ((continuous_quadratic c).comp continuous_subtype_val)
        (fun x => by
          have hx : quadratic c (x : ℂ) ∈ escapeOpen c := by
            have := escapeOpen_iterate (c := c) (z := (x : ℂ)) x.2 1
            simpa [Function.iterate_one] using this
          exact escapeOpen_coe_ne_zero c ⟨quadratic c (x : ℂ), hx⟩) p
      = 2 * wind (fun x : escapeOpen c => (x : ℂ)) (by fun_prop)
          (fun x => escapeOpen_coe_ne_zero c x) p := by
  simpa [quadratic] using
    (wind_quadratic (X := escapeOpen c) c (fun x : escapeOpen c => (x : ℂ))
      continuous_subtype_val (fun x => escapeOpen_norm_c_lt_norm_sq c x) p)

/-- If `‖a‖ < ‖w‖`, then the straight radial correction from `w` to `w-a` lies in the right
half-plane after normalization by `w`. -/
theorem one_sub_div_re_pos_of_norm_lt {a w : ℂ} (hw : w ≠ 0) (hlt : ‖a‖ < ‖w‖) :
    0 < (1 - a / w).re := by
  let u : ℂ := w⁻¹ * ((w - a) - w)
  have htarget : 1 - a / w = w⁻¹ * (w - a) := by
    rw [div_eq_mul_inv]
    calc
      1 - a * w⁻¹ = w⁻¹ * w - a * w⁻¹ := by rw [inv_mul_cancel₀ hw]
      _ = w⁻¹ * (w - a) := by ring
  have hdecomp : w⁻¹ * (w - a) = 1 + u := by
    calc
      w⁻¹ * (w - a) = w⁻¹ * (w + ((w - a) - w)) := by ring
      _ = w⁻¹ * w + w⁻¹ * ((w - a) - w) := by ring
      _ = 1 + u := by rw [inv_mul_cancel₀ hw]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hu_norm : ‖u‖ < 1 := by
    have hmul : ‖u‖ = ‖w‖⁻¹ * ‖(w - a) - w‖ := by
      simp [u, norm_inv]
    have hdiff : ‖(w - a) - w‖ = ‖a‖ := by
      rw [show (w - a) - w = -a by ring, norm_neg]
    rw [hmul, hdiff]
    exact (inv_mul_lt_iff₀ hwpos).mpr (by simpa using hlt)
  have hre_lower : -‖u‖ ≤ u.re := (abs_le.mp (Complex.abs_re_le_norm u)).1
  rw [htarget, hdecomp]
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- **One-step closed-lift parity over the far field.** If `g²+c` stays in `escapeOpen c`, then the
downstairs loop `g²+c` has twice the winding of the closed lift `g`. Algebraically,
`g² = (g²+c) · (1 - c/(g²+c))`; the correction has positive real part because `‖c‖ < ‖g²+c‖` on
`escapeOpen c`, hence contributes no winding. -/
theorem wind_quadratic_of_image_escapeOpen {X : Type*} [TopologicalSpace X]
    (c : ℂ) (g : X → ℂ) (hg : Continuous g)
    (hesc : ∀ x, quadratic c (g x) ∈ escapeOpen c) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => quadratic c (g x)) ((continuous_quadratic c).comp hg)
        (fun x => escapeOpen_coe_ne_zero c ⟨quadratic c (g x), hesc x⟩) p
      = 2 * wind g hg (fun x => by
          intro hx
          have hbad := hesc x
          rw [hx] at hbad
          simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
            escapeOpen, Set.mem_setOf_eq] at hbad
          exact not_lt_of_ge (le_max_right 2 ‖c‖) hbad) p := by
  set H : X → ℂ := fun x => quadratic c (g x) with hHdef
  have hHcont : Continuous H := ((continuous_quadratic c).comp hg)
  have hHne : ∀ x, H x ≠ 0 := fun x => by
    rw [hHdef]
    exact escapeOpen_coe_ne_zero c ⟨quadratic c (g x), hesc x⟩
  have gne : ∀ x, g x ≠ 0 := fun x => by
    intro hx
    have hbad := hesc x
    rw [hx] at hbad
    simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      escapeOpen, Set.mem_setOf_eq] at hbad
    exact not_lt_of_ge (le_max_right 2 ‖c‖) hbad
  set C : X → ℂ := fun x => 1 - c / H x with hCdef
  have hCcont : Continuous C := by
    rw [hCdef]
    fun_prop (disch := exact hHne _)
  have hCpos : ∀ x, 0 < (C x).re := fun x => by
    rw [hCdef]
    exact one_sub_div_re_pos_of_norm_lt (hHne x)
      (lt_of_le_of_lt (le_max_right 2 ‖c‖) (by
        simpa [hHdef, escapeOpen, Set.mem_setOf_eq] using hesc x))
  have hCne : ∀ x, C x ≠ 0 := fun x hx => by
    have hpos := hCpos x
    rw [hx] at hpos
    simp at hpos
  have hCslit : ∀ t : I, C (p t) ∈ Complex.slitPlane := fun t => by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (hCpos (p t))
  have hfun : (fun x => g x ^ (2 : ℕ)) = fun x => H x * C x := by
    funext x
    rw [hHdef, hCdef]
    show g x ^ (2 : ℕ) = quadratic c (g x) * (1 - c / quadratic c (g x))
    rw [mul_sub, mul_one, mul_div_cancel₀ c (by
      exact escapeOpen_coe_ne_zero c ⟨quadratic c (g x), hesc x⟩)]
    simp [quadratic]
  have hsquare :
      wind (fun x => g x ^ (2 : ℕ)) (hg.pow 2) (fun x => pow_ne_zero 2 (gne x)) p
        = wind H hHcont hHne p := by
    rw [wind_congr hfun (hg.pow 2) (fun x => pow_ne_zero 2 (gne x))
      (hHcont.mul hCcont) (fun x => mul_ne_zero (hHne x) (hCne x)) p]
    rw [wind_mul H C hHcont hCcont hHne hCne p]
    rw [wind_zero_of_slitPlane C hCcont hCne p hCslit, add_zero]
  have hpow := wind_pow g hg gne 2 p
  rw [hpow] at hsquare
  calc
    wind (fun x => quadratic c (g x)) ((continuous_quadratic c).comp hg)
        (fun x => escapeOpen_coe_ne_zero c ⟨quadratic c (g x), hesc x⟩) p
        = wind H hHcont hHne p := by
          exact wind_congr hHdef.symm ((continuous_quadratic c).comp hg)
            (fun x => escapeOpen_coe_ne_zero c ⟨quadratic c (g x), hesc x⟩) hHcont hHne p
    _ = 2 * wind g hg gne p := hsquare.symm
    _ = 2 * wind g hg (fun x => by
          intro hx
          have hbad := hesc x
          rw [hx] at hbad
          simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
            escapeOpen, Set.mem_setOf_eq] at hbad
          exact not_lt_of_ge (le_max_right 2 ‖c‖) hbad) p := by
          rfl

/-- The `n`-th quadratic iterate as a self-map of the far-field escape set. -/
noncomputable def quadraticIterateEscapeOpenMap (c : ℂ) (n : ℕ) : C(escapeOpen c, escapeOpen c) where
  toFun x := ⟨(quadratic c)^[n] (x : ℂ), escapeOpen_iterate x.2 n⟩
  continuous_toFun :=
    ((((continuous_quadratic c).iterate n).comp continuous_subtype_val).subtype_mk
      (fun x => escapeOpen_iterate x.2 n))

/-- Continuity of the Böttcher coordinate after an escape-open iterate. -/
theorem continuous_bottcherCoord_iterate_escapeOpen (c : ℂ) (n : ℕ) :
    Continuous fun x : escapeOpen c => bottcherCoord c ((quadratic c)^[n] (x : ℂ)) := by
  have hF : Continuous fun x : escapeOpen c => (quadratic c)^[n] (x : ℂ) :=
    ((continuous_quadratic c).iterate n).comp continuous_subtype_val
  exact (analyticOnNhd_bottcherCoord_full c).continuousOn.comp_continuous hF
    (fun x => escapeOpen_iterate x.2 n)

/-- **Far-field degree `2ⁿ`.** Iterating the quadratic map on `escapeOpen c` multiplies position
winding by `2ⁿ`. This is the formal far-field version of the dynamical degree input used before
lifting roots down the escape-level tower. -/
theorem wind_quadratic_iterate_escapeOpen (c : ℂ) (n : ℕ) {x₀ : escapeOpen c}
    (p : Path x₀ x₀) :
    wind (fun x : escapeOpen c => (quadratic c)^[n] (x : ℂ))
        (((continuous_quadratic c).iterate n).comp continuous_subtype_val)
        (fun x => escapeOpen_coe_ne_zero c
          ⟨(quadratic c)^[n] (x : ℂ), escapeOpen_iterate x.2 n⟩) p
      = (2 : ℤ) ^ n * wind (fun x : escapeOpen c => (x : ℂ)) continuous_subtype_val
          (fun x => escapeOpen_coe_ne_zero c x) p := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hbig : ∀ x : escapeOpen c, ‖c‖ < ‖(quadratic c)^[n] (x : ℂ)‖ ^ (2 : ℕ) :=
        fun x => escapeOpen_norm_c_lt_norm_sq c
          ⟨(quadratic c)^[n] (x : ℂ), escapeOpen_iterate x.2 n⟩
      have hquad :=
        wind_quadratic (X := escapeOpen c) c
          (fun x : escapeOpen c => (quadratic c)^[n] (x : ℂ))
          (((continuous_quadratic c).iterate n).comp continuous_subtype_val) hbig p
      calc
        wind (fun x : escapeOpen c => (quadratic c)^[n + 1] (x : ℂ))
            (((continuous_quadratic c).iterate (n + 1)).comp continuous_subtype_val)
            (fun x => escapeOpen_coe_ne_zero c
              ⟨(quadratic c)^[n + 1] (x : ℂ), escapeOpen_iterate x.2 (n + 1)⟩) p
            = 2 * wind (fun x : escapeOpen c => (quadratic c)^[n] (x : ℂ))
                (((continuous_quadratic c).iterate n).comp continuous_subtype_val)
                (fun x => escapeOpen_coe_ne_zero c
                  ⟨(quadratic c)^[n] (x : ℂ), escapeOpen_iterate x.2 n⟩) p := by
              simpa [quadratic, Function.iterate_succ_apply'] using hquad
        _ = 2 * ((2 : ℤ) ^ n * wind (fun x : escapeOpen c => (x : ℂ))
                continuous_subtype_val (fun x => escapeOpen_coe_ne_zero c x) p) := by
              rw [ih]
        _ = (2 : ℤ) ^ (n + 1) * wind (fun x : escapeOpen c => (x : ℂ))
                continuous_subtype_val (fun x => escapeOpen_coe_ne_zero c x) p := by
              ring

/-- **Far-field Böttcher iterate winding.** On `escapeOpen c`, the loop
`z ↦ bottcherCoord c (f_c^[n] z)` has winding `2ⁿ` times the position winding. This is the paper's
degree computation after removing the exponential Böttcher factor. -/
theorem wind_bottcherCoord_iterate_escapeOpen (c : ℂ) (n : ℕ) {x₀ : escapeOpen c}
    (p : Path x₀ x₀) :
    wind (fun x : escapeOpen c => bottcherCoord c ((quadratic c)^[n] (x : ℂ)))
        (continuous_bottcherCoord_iterate_escapeOpen c n)
        (fun _ => bottcherCoord_ne_zero c _) p
      = (2 : ℤ) ^ n * wind (fun x : escapeOpen c => (x : ℂ)) continuous_subtype_val
          (fun x => escapeOpen_coe_ne_zero c x) p := by
  let F : C(escapeOpen c, escapeOpen c) := quadraticIterateEscapeOpenMap c n
  have hbridge := wind_bottcherCoord_comp_eq_wind_coe c F p
    (continuous_bottcherCoord_iterate_escapeOpen c n)
  calc
    wind (fun x : escapeOpen c => bottcherCoord c ((quadratic c)^[n] (x : ℂ)))
        (continuous_bottcherCoord_iterate_escapeOpen c n)
        (fun _ => bottcherCoord_ne_zero c _) p
        = wind (fun x : escapeOpen c => (F x : ℂ)) (continuous_subtype_val.comp F.continuous)
            (fun x => escapeOpen_coe_ne_zero c (F x)) p := by
          simpa [F, quadraticIterateEscapeOpenMap] using hbridge
    _ = (2 : ℤ) ^ n * wind (fun x : escapeOpen c => (x : ℂ)) continuous_subtype_val
          (fun x => escapeOpen_coe_ne_zero c x) p := by
          simpa [F, quadraticIterateEscapeOpenMap] using wind_quadratic_iterate_escapeOpen c n p

end Bottcher
