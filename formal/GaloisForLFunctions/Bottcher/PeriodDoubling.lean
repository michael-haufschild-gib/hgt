/-
# Period-doubling of the √-branch: `L_1(t+2πi) = −L_1(t)`

The base of the escape-level monodromy. Along the segment `s ↦ t + 2πi·s` in the half-plane `H`, the
`L_0 = bottcherCoord∘exp` loop has winding `1` (odd) — the circle generator pushed through the
winding-preserving `bottcherCoord`. Since `L_1² = L_0`, if `L_1` were `2πi`-periodic its normalized
loop would square to the `L_0`-loop, forcing winding `1` to be even — impossible. Hence the √ flips:
`L_1(t+2πi) = −L_1(t)`. This is `FLIP_0`, the base case driving the exact `2ⁿ·2πi` period of the tower.
-/
import GaloisForLFunctions.Bottcher.UniversalCover
import GaloisForLFunctions.Bottcher.BottcherWinding
import GaloisForLFunctions.Bottcher.CircleDegree

open Topology unitInterval Pi1CMinusZero

namespace Bottcher

variable {c : ℂ}

/-- The exponential of a `2πi`-vertical shift stays in `escapeOpen` (same modulus). -/
theorem exp_shift_mem_escapeOpen {t : ℂ} (ht : t ∈ coverPlane c) (s : ℝ) :
    Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) ∈ escapeOpen c := by
  have hmod : ‖Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))‖ = ‖Complex.exp t‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have ht' : Complex.exp t ∈ escapeOpen c := ht
  simp only [escapeOpen, Set.mem_setOf_eq] at ht' ⊢
  rwa [hmod]

/-- `exp` is `2πi`-periodic: `exp (t + 2πi) = exp t`. -/
theorem exp_add_two_pi (t : ℂ) :
    Complex.exp (t + 2 * (Real.pi : ℂ) * Complex.I) = Complex.exp t := by
  rw [Complex.exp_add]
  have : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩
  rw [this, mul_one]

/-- A purely-imaginary shift preserves membership in `escapeOpen` (same modulus). -/
theorem exp_add_im_mem {t : ℂ} (ht : t ∈ coverPlane c) {w : ℂ} (hw : w.re = 0) :
    Complex.exp (t + w) ∈ escapeOpen c := by
  have hmod : ‖Complex.exp (t + w)‖ = ‖Complex.exp t‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]; congr 1
    rw [Complex.add_re, hw, add_zero]
  have ht' : Complex.exp t ∈ escapeOpen c := ht
  simp only [escapeOpen, Set.mem_setOf_eq] at ht' ⊢
  rwa [hmod]

/-- The tower power collapses to the base: `L_m ^ (2^m) = L_0`. -/
theorem Lroot_pow (m : ℕ) {z : ℂ} (hz : z ∈ coverPlane c) :
    (Lroot c m z) ^ (2 ^ m) = Lroot c 0 z := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : (Lroot c (k + 1) z) ^ 2 = Lroot c k z := Lroot_succ_sq c k hz
    calc (Lroot c (k + 1) z) ^ (2 ^ (k + 1))
        = ((Lroot c (k + 1) z) ^ 2) ^ (2 ^ k) := by
          rw [← pow_mul]; congr 1; rw [pow_succ]; ring
      _ = (Lroot c k z) ^ (2 ^ k) := by rw [h2]
      _ = Lroot c 0 z := ih

/-- Vertical shifts stay in the covering half-plane `H`. -/
theorem shift_mem_coverPlane {t : ℂ} (ht : t ∈ coverPlane c) (s : ℝ) :
    t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ) ∈ coverPlane c :=
  exp_shift_mem_escapeOpen ht s

/-- **`FLIP_0`: the √-branch flips over one period.** `L_1(t + 2πi) = − L_1(t)`. -/
theorem Lroot_one_anti {t : ℂ} (ht : t ∈ coverPlane c) :
    Lroot c 1 (t + 2 * (Real.pi : ℂ) * Complex.I) = - Lroot c 1 t := by
  -- the shifted basepoint is in `H`, and `exp` is periodic there
  have ht2 : t + 2 * (Real.pi : ℂ) * Complex.I ∈ coverPlane c := by
    have := shift_mem_coverPlane ht 1
    simpa using this
  -- `L_1(t+2πi)² = L_1(t)²` (both equal `L_0(t) = bottcherCoord(exp t)`)
  have e1 : (Lroot c 1 (t + 2 * (Real.pi : ℂ) * Complex.I)) ^ 2
      = Lroot c 0 (t + 2 * (Real.pi : ℂ) * Complex.I) := Lroot_succ_sq c 0 ht2
  have e2 : (Lroot c 1 t) ^ 2 = Lroot c 0 t := Lroot_succ_sq c 0 ht
  have hsq : (Lroot c 1 (t + 2 * (Real.pi : ℂ) * Complex.I)) ^ 2 = (Lroot c 1 t) ^ 2 := by
    rw [e1, e2, Lroot_zero, Lroot_zero, exp_add_two_pi]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · -- the `+` case: derive a parity contradiction and discharge by `exfalso`
    exfalso
    -- continuity / nonvanishing data on the `escapeOpen` subtype
    have hgId : Continuous (fun x : escapeOpen c => (x : ℂ)) := continuous_subtype_val
    have hgIdne : ∀ x : escapeOpen c, (x : ℂ) ≠ 0 := by
      intro x hx0
      have hx := x.2
      rw [hx0] at hx
      simp only [escapeOpen, Set.mem_setOf_eq, norm_zero] at hx
      exact absurd hx (not_lt.mpr (le_trans (by norm_num) (le_max_left 2 ‖c‖)))
    have hgB : Continuous (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) :=
      (analyticOnNhd_bottcherCoord_full c).continuousOn.restrict
    have hgBne : ∀ x : escapeOpen c, bottcherCoord c (x : ℂ) ≠ 0 := fun x => bottcherCoord_ne_zero c _
    -- the circle loop `s ↦ exp(t + 2πi·s)` inside `escapeOpen`
    let xhat : escapeOpen c := ⟨Complex.exp t, ht⟩
    have hone : (((1 : I) : ℝ) : ℂ) = 1 := by simp
    have hcirc_cont : Continuous fun s : I =>
        (⟨Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)),
          exp_shift_mem_escapeOpen ht (s : ℝ)⟩ : escapeOpen c) :=
      (Complex.continuous_exp.comp
        (by fun_prop : Continuous fun s : I => t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))).subtype_mk
        (fun s => exp_shift_mem_escapeOpen ht (s : ℝ))
    let Chat : Path xhat xhat :=
      { toFun := fun s => ⟨Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)),
          exp_shift_mem_escapeOpen ht (s : ℝ)⟩
        continuous_toFun := hcirc_cont
        source' := by
          apply Subtype.ext
          show Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ)) = Complex.exp t
          simp
        target' := by
          apply Subtype.ext
          show Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) = Complex.exp t
          rw [hone, mul_one, exp_add_two_pi] }
    -- the normalized `L_0`-loop `q0 = transLoop bottcherCoord Chat`, of winding `1`
    set q0 : Path one_cs one_cs :=
      transLoop (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne Chat with hq0def
    have hq0deg : degZ ⟦q0⟧ = 1 := by
      have hbrick : wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne Chat
          = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat :=
        wind_bottcherCoord_eq_wind_id c Chat hgB hgBne hgId hgIdne
      have hid : transLoop (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat = circleLoop := by
        apply Path.ext; funext s; apply Subtype.ext
        show (Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))) / Complex.exp t
          = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
        rw [add_comm t, Complex.exp_add, mul_div_assoc, div_self (Complex.exp_ne_zero t), mul_one]
      calc degZ ⟦q0⟧ = wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne Chat := rfl
        _ = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat := hbrick
        _ = degZ ⟦transLoop (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat⟧ := rfl
        _ = degZ ⟦circleLoop⟧ := by rw [hid]
        _ = 1 := degZ_circleLoop
    -- the normalized `L_1`-loop `q1` (a genuine loop thanks to `h`)
    have hL1ne : ∀ s : I, Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) ≠ 0 :=
      fun s => Lroot_ne_zero c 1 (shift_mem_coverPlane ht (s : ℝ))
    have hL1tne : Lroot c 1 t ≠ 0 := Lroot_ne_zero c 1 ht
    have hshift_cont : Continuous fun s : I => t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ) := by
      fun_prop
    have hLcomp : Continuous fun s : I =>
        Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) :=
      (Lroot_analytic c 1).continuousOn.comp_continuous hshift_cont
        (fun s => shift_mem_coverPlane ht (s : ℝ))
    have hq1cont : Continuous fun s : I =>
        (⟨Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / Lroot c 1 t,
          div_ne_zero (hL1ne s) hL1tne⟩ : Cs) :=
      (hLcomp.div_const (Lroot c 1 t)).subtype_mk (fun s => div_ne_zero (hL1ne s) hL1tne)
    let q1 : Path one_cs one_cs :=
      { toFun := fun s => ⟨Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / Lroot c 1 t,
          div_ne_zero (hL1ne s) hL1tne⟩
        continuous_toFun := hq1cont
        source' := by
          apply Subtype.ext
          show Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ)) / Lroot c 1 t = (1 : ℂ)
          simp [div_self hL1tne]
        target' := by
          apply Subtype.ext
          show Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) / Lroot c 1 t = (1 : ℂ)
          rw [hone, mul_one, h, div_self hL1tne] }
    -- `sqLoop q1 = q0`, so `1 = degZ q0 = 2 · degZ q1` — impossible
    have hsqeq : sqLoop q1 = q0 := by
      apply Path.ext
      funext s
      apply Subtype.ext
      show (Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / Lroot c 1 t) ^ 2
        = bottcherCoord c (Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)))
          / bottcherCoord c (Complex.exp t)
      have hnum : (Lroot c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))) ^ 2
          = bottcherCoord c (Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))) := by
        have hh := Lroot_succ_sq c 0 (shift_mem_coverPlane ht (s : ℝ))
        rw [Lroot_zero] at hh; exact hh
      have hden : (Lroot c 1 t) ^ 2 = bottcherCoord c (Complex.exp t) := by
        have hh := Lroot_succ_sq c 0 ht; rw [Lroot_zero] at hh; exact hh
      rw [div_pow, hnum, hden]
    have hfin : (1 : ℤ) = 2 * degZ ⟦q1⟧ := by
      rw [← hq0deg, ← hsqeq, degZ_sqLoop]
    omega

  · exact h

/-- **Base sheet-swap for the `ρ` tower.** Over one vertical period, the first square-root lift changes
sheet: `ρ₁(t + 2πi) = -ρ₁(t)`. The proof is the same parity obstruction as `Lroot_one_anti`, but the
odd loop is now `s ↦ exp(t + 2πis) - c`; it has winding one because it is the large circle
`exp(t + 2πis)` multiplied by the windingless correction `1 - c / exp(t + 2πis)`. -/
theorem rho_one_anti (hc : ∀ n, c ∉ escapeLevel c n) {t : ℂ} (ht : t ∈ coverPlane c) :
    rho c 1 (t + 2 * (Real.pi : ℂ) * Complex.I) = -rho c 1 t := by
  have ht2 : t + 2 * (Real.pi : ℂ) * Complex.I ∈ coverPlane c := by
    have := shift_mem_coverPlane ht 1
    simpa using this
  have e1 : (rho c 1 (t + 2 * (Real.pi : ℂ) * Complex.I)) ^ 2
      = rho c 0 (t + 2 * (Real.pi : ℂ) * Complex.I) - c := rho_succ_sq c hc 0 ht2
  have e2 : (rho c 1 t) ^ 2 = rho c 0 t - c := rho_succ_sq c hc 0 ht
  have hsq : (rho c 1 (t + 2 * (Real.pi : ℂ) * Complex.I)) ^ 2 = (rho c 1 t) ^ 2 := by
    rw [e1, e2, rho_zero, exp_add_two_pi]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exfalso
    have hgId : Continuous (fun x : escapeOpen c => (x : ℂ)) := continuous_subtype_val
    have hgIdne : ∀ x : escapeOpen c, (x : ℂ) ≠ 0 := fun x => escapeOpen_coe_ne_zero c x
    let xhat : escapeOpen c := ⟨Complex.exp t, ht⟩
    have hone : (((1 : I) : ℝ) : ℂ) = 1 := by simp
    have hcirc_cont : Continuous fun s : I =>
        (⟨Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)),
          exp_shift_mem_escapeOpen ht (s : ℝ)⟩ : escapeOpen c) :=
      (Complex.continuous_exp.comp
        (by fun_prop : Continuous fun s : I => t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))).subtype_mk
        (fun s => exp_shift_mem_escapeOpen ht (s : ℝ))
    let Chat : Path xhat xhat :=
      { toFun := fun s => ⟨Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)),
          exp_shift_mem_escapeOpen ht (s : ℝ)⟩
        continuous_toFun := hcirc_cont
        source' := by
          apply Subtype.ext
          show Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ)) = Complex.exp t
          simp
        target' := by
          apply Subtype.ext
          show Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) = Complex.exp t
          rw [hone, mul_one, exp_add_two_pi] }
    let G : escapeOpen c → ℂ := fun x => (x : ℂ) - c
    have hGcont : Continuous G := by fun_prop
    have hGne : ∀ x : escapeOpen c, G x ≠ 0 := by
      intro x hx0
      have hxc : (x : ℂ) = c := sub_eq_zero.mp hx0
      have hcEsc : c ∈ escapeOpen c := by
        simpa only [hxc] using x.2
      exact (hc 0) (by rwa [escapeLevel_zero])
    let C : escapeOpen c → ℂ := fun x => 1 - c / (x : ℂ)
    have hCcont : Continuous C := by
      dsimp [C]
      fun_prop (disch := exact escapeOpen_coe_ne_zero c _)
    have hCpos : ∀ x : escapeOpen c, 0 < (C x).re := by
      intro x
      dsimp [C]
      exact one_sub_div_re_pos_of_norm_lt (escapeOpen_coe_ne_zero c x)
        (lt_of_le_of_lt (le_max_right 2 ‖c‖) x.2)
    have hCne : ∀ x : escapeOpen c, C x ≠ 0 := by
      intro x hx0
      have hxpos := hCpos x
      rw [hx0] at hxpos
      simp at hxpos
    have hCslit : ∀ s : I, C (Chat s) ∈ Complex.slitPlane := by
      intro s
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (hCpos (Chat s))
    set q0 : Path one_cs one_cs := transLoop G hGcont hGne Chat with hq0def
    have hq0deg : degZ ⟦q0⟧ = 1 := by
      have hGfun : G = fun x : escapeOpen c => (x : ℂ) * C x := by
        funext x
        dsimp [G, C]
        rw [mul_sub, mul_one, mul_div_cancel₀ c (escapeOpen_coe_ne_zero c x)]
      have hGwind :
          wind G hGcont hGne Chat
            = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat
              + wind C hCcont hCne Chat := by
        rw [wind_congr hGfun hGcont hGne (hgId.mul hCcont)
          (fun x => mul_ne_zero (hgIdne x) (hCne x)) Chat]
        exact wind_mul (fun x : escapeOpen c => (x : ℂ)) C hgId hCcont hgIdne hCne Chat
      have hid : transLoop (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat = circleLoop := by
        apply Path.ext; funext s; apply Subtype.ext
        show (Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))) / Complex.exp t
          = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
        rw [add_comm t, Complex.exp_add, mul_div_assoc, div_self (Complex.exp_ne_zero t), mul_one]
      calc degZ ⟦q0⟧ = wind G hGcont hGne Chat := rfl
        _ = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat
              + wind C hCcont hCne Chat := hGwind
        _ = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat + 0 := by
              rw [wind_zero_of_slitPlane C hCcont hCne Chat hCslit]
        _ = degZ ⟦transLoop (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat⟧ := by
              rw [add_zero]
              rfl
        _ = degZ ⟦circleLoop⟧ := by rw [hid]
        _ = 1 := degZ_circleLoop
    have hρ1_ne_of_mem : ∀ {u : ℂ}, u ∈ coverPlane c → rho c 1 u ≠ 0 := by
      intro u hu hzero
      have hsq0 := rho_succ_sq c hc 0 hu
      rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), rho_zero] at hsq0
      have hcu : Complex.exp u = c := by
        exact sub_eq_zero.mp hsq0.symm
      have hcEsc : c ∈ escapeOpen c := by
        change Complex.exp u ∈ escapeOpen c at hu
        simpa only [hcu] using hu
      exact (hc 0) (by rwa [escapeLevel_zero])
    have hρ1ne : ∀ s : I, rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) ≠ 0 :=
      fun s => hρ1_ne_of_mem (shift_mem_coverPlane ht (s : ℝ))
    have hρ1tne : rho c 1 t ≠ 0 := hρ1_ne_of_mem ht
    have hshift_cont : Continuous fun s : I => t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ) := by
      fun_prop
    have hρcomp : Continuous fun s : I =>
        rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) :=
      (rho_analytic c hc 1).continuousOn.comp_continuous hshift_cont
        (fun s => shift_mem_coverPlane ht (s : ℝ))
    have hq1cont : Continuous fun s : I =>
        (⟨rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / rho c 1 t,
          div_ne_zero (hρ1ne s) hρ1tne⟩ : Cs) :=
      (hρcomp.div_const (rho c 1 t)).subtype_mk (fun s => div_ne_zero (hρ1ne s) hρ1tne)
    let q1 : Path one_cs one_cs :=
      { toFun := fun s => ⟨rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / rho c 1 t,
          div_ne_zero (hρ1ne s) hρ1tne⟩
        continuous_toFun := hq1cont
        source' := by
          apply Subtype.ext
          show rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ)) / rho c 1 t = (1 : ℂ)
          simp [div_self hρ1tne]
        target' := by
          apply Subtype.ext
          show rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) / rho c 1 t = (1 : ℂ)
          rw [hone, mul_one, h, div_self hρ1tne] }
    have hsqeq : sqLoop q1 = q0 := by
      apply Path.ext
      funext s
      apply Subtype.ext
      show (rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / rho c 1 t) ^ 2
        = (Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) - c) / (Complex.exp t - c)
      have hnum : (rho c 1 (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))) ^ 2
          = Complex.exp (t + (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) - c := by
        have hh := rho_succ_sq c hc 0 (shift_mem_coverPlane ht (s : ℝ))
        rw [rho_zero] at hh
        exact hh
      have hden : (rho c 1 t) ^ 2 = Complex.exp t - c := by
        have hh := rho_succ_sq c hc 0 ht
        rw [rho_zero] at hh
        exact hh
      rw [div_pow, hnum, hden]
    have hfin : (1 : ℤ) = 2 * degZ ⟦q1⟧ := by
      rw [← hq0deg, ← hsqeq, degZ_sqLoop]
    omega
  · exact h

/-! ## General period-doubling at every level -/

/-- The level-`m` vertical period `2^m · 2πi` is purely imaginary. -/
theorem vshift_re_zero (m : ℕ) :
    (((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).re = 0 := by
  have h : ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = (((2 ^ m : ℕ) : ℝ) * (2 * Real.pi) : ℝ) * Complex.I := by push_cast; ring
  rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- `exp(2^m · 2πi) = 1`. -/
theorem exp_pow_period (m : ℕ) :
    Complex.exp (((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_eq_one_iff]; exact ⟨(2 ^ m : ℤ), by push_cast; ring⟩

/-- `exp(t + 2^m · 2πi) = exp t`. -/
theorem exp_add_pow_period (m : ℕ) (t : ℂ) :
    Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = Complex.exp t := by
  rw [Complex.exp_add, exp_pow_period, mul_one]

/-- **`FLIP_m` given the level-`m` period.** If `L_m` has period `2^m·2πi`, then `L_{m+1}` flips over
that period: `L_{m+1}(t + 2^m·2πi) = − L_{m+1}(t)`. The `L_m`-loop over the period has winding `1`
(it is the `2^m`-th root of the winding-`2^m` `L_0`-loop), so a periodic `L_{m+1}` would force `1` to
be even. -/
theorem Lroot_flip_of_period (m : ℕ)
    (hper : ∀ {u : ℂ}, u ∈ coverPlane c →
      Lroot c m (u + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = Lroot c m u)
    {t : ℂ} (ht : t ∈ coverPlane c) :
    Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
      = - Lroot c (m + 1) t := by
  have hPsim : ∀ s : ℝ,
      (((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)).re = 0 := by
    intro s; rw [Complex.mul_re, vshift_re_zero, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  have ht2 : t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ∈ coverPlane c :=
    exp_add_im_mem ht (vshift_re_zero m)
  have e1 : (Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) ^ 2
      = Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := Lroot_succ_sq c m ht2
  have e2 : (Lroot c (m + 1) t) ^ 2 = Lroot c m t := Lroot_succ_sq c m ht
  have hsq : (Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) ^ 2
      = (Lroot c (m + 1) t) ^ 2 := by rw [e1, e2, hper ht]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exfalso
    have hgId : Continuous (fun x : escapeOpen c => (x : ℂ)) := continuous_subtype_val
    have hgIdne : ∀ x : escapeOpen c, (x : ℂ) ≠ 0 := by
      intro x hx0
      have hx : (x : ℂ) ∈ escapeOpen c := x.2
      rw [hx0] at hx
      simp only [escapeOpen, Set.mem_setOf_eq, norm_zero] at hx
      exact absurd hx (not_lt.mpr (le_trans (by norm_num : (0:ℝ) ≤ 2) (le_max_left 2 ‖c‖)))
    have hgB : Continuous (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) :=
      (analyticOnNhd_bottcherCoord_full c).continuousOn.restrict
    have hgBne : ∀ x : escapeOpen c, bottcherCoord c (x : ℂ) ≠ 0 := fun x => bottcherCoord_ne_zero c _
    let xhat : escapeOpen c := ⟨Complex.exp t, ht⟩
    have hcirc_cont : Continuous fun s : I =>
        (⟨Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)),
          exp_add_im_mem ht (hPsim (s : ℝ))⟩ : escapeOpen c) :=
      (Complex.continuous_exp.comp
        (by fun_prop : Continuous fun s : I =>
          t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))).subtype_mk
        (fun s => exp_add_im_mem ht (hPsim (s : ℝ)))
    let Chat : Path xhat xhat :=
      { toFun := fun s => ⟨Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)),
          exp_add_im_mem ht (hPsim (s : ℝ))⟩
        continuous_toFun := hcirc_cont
        source' := by
          apply Subtype.ext
          show Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ))
            = Complex.exp t
          simp
        target' := by
          apply Subtype.ext
          show Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ))
            = Complex.exp t
          rw [Set.Icc.coe_one, Complex.ofReal_one, mul_one]; exact exp_add_pow_period m t }
    set q0 : Path one_cs one_cs :=
      transLoop (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne Chat with hq0def
    have hq0deg : degZ ⟦q0⟧ = ((2 ^ m : ℕ) : ℤ) := by
      have hbrick : wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne Chat
          = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat :=
        wind_bottcherCoord_eq_wind_id c Chat hgB hgBne hgId hgIdne
      have hid : transLoop (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat
          = circleLoopNat (2 ^ m) := by
        apply Path.ext; funext s; apply Subtype.ext
        show Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
            / Complex.exp t
          = Complex.exp (((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
        rw [add_comm t, Complex.exp_add, mul_div_assoc, div_self (Complex.exp_ne_zero t), mul_one]
      calc degZ ⟦q0⟧
          = wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne Chat := rfl
        _ = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat := hbrick
        _ = degZ ⟦transLoop (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne Chat⟧ := rfl
        _ = degZ ⟦circleLoopNat (2 ^ m)⟧ := by rw [hid]
        _ = ((2 ^ m : ℕ) : ℤ) := degZ_circleLoopNat (2 ^ m)
    -- normalized `L_m`-loop, winding `1`
    have hLmne : ∀ s : I,
        Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) ≠ 0 :=
      fun s => Lroot_ne_zero c m (exp_add_im_mem ht (hPsim (s : ℝ)))
    have hLmtne : Lroot c m t ≠ 0 := Lroot_ne_zero c m ht
    have hq0mcont : Continuous fun s : I =>
        (⟨Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / Lroot c m t,
          div_ne_zero (hLmne s) hLmtne⟩ : Cs) :=
      (((Lroot_analytic c m).continuousOn.comp_continuous
        (by fun_prop : Continuous fun s : I =>
          t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
        (fun s => exp_add_im_mem ht (hPsim (s : ℝ)))).div_const _).subtype_mk _
    let q0m : Path one_cs one_cs :=
      { toFun := fun s =>
          ⟨Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / Lroot c m t,
            div_ne_zero (hLmne s) hLmtne⟩
        continuous_toFun := hq0mcont
        source' := by
          apply Subtype.ext
          show Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ))
              / Lroot c m t = (1 : ℂ)
          simp [div_self hLmtne]
        target' := by
          apply Subtype.ext
          show Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ))
              / Lroot c m t = (1 : ℂ)
          rw [Set.Icc.coe_one, Complex.ofReal_one, mul_one, hper ht, div_self hLmtne] }
    have hpow : powLoop (2 ^ m) q0m = q0 := by
      apply Path.ext; funext s; apply Subtype.ext
      rw [powLoop_apply]
      show (Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
            / Lroot c m t) ^ (2 ^ m)
        = bottcherCoord c (Complex.exp (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)))
            / bottcherCoord c (Complex.exp t)
      rw [div_pow, Lroot_pow m (exp_add_im_mem ht (hPsim (s : ℝ))), Lroot_pow m ht,
        Lroot_zero, Lroot_zero]
    have hq0mdeg : degZ ⟦q0m⟧ = 1 := by
      refine degZ_eq_one_of_powLoop_eq_natCast (2 ^ m) q0m (by positivity) ?_
      rw [hpow, hq0deg]
    -- normalized `L_{m+1}`-loop (a loop thanks to `h`); its square is the `L_m`-loop
    have hL1ne : ∀ s : I,
        Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) ≠ 0 :=
      fun s => Lroot_ne_zero c (m + 1) (exp_add_im_mem ht (hPsim (s : ℝ)))
    have hL1tne : Lroot c (m + 1) t ≠ 0 := Lroot_ne_zero c (m + 1) ht
    have hq1cont : Continuous fun s : I =>
        (⟨Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
            / Lroot c (m + 1) t, div_ne_zero (hL1ne s) hL1tne⟩ : Cs) :=
      (((Lroot_analytic c (m + 1)).continuousOn.comp_continuous
        (by fun_prop : Continuous fun s : I =>
          t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
        (fun s => exp_add_im_mem ht (hPsim (s : ℝ)))).div_const _).subtype_mk _
    let q1 : Path one_cs one_cs :=
      { toFun := fun s =>
          ⟨Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
              / Lroot c (m + 1) t, div_ne_zero (hL1ne s) hL1tne⟩
        continuous_toFun := hq1cont
        source' := by
          apply Subtype.ext
          show Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ))
              / Lroot c (m + 1) t = (1 : ℂ)
          simp [div_self hL1tne]
        target' := by
          apply Subtype.ext
          show Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ))
              / Lroot c (m + 1) t = (1 : ℂ)
          rw [Set.Icc.coe_one, Complex.ofReal_one, mul_one, h, div_self hL1tne] }
    have hsqeq : sqLoop q1 = q0m := by
      apply Path.ext; funext s; apply Subtype.ext
      show (Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
            / Lroot c (m + 1) t) ^ 2
        = Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) / Lroot c m t
      have hnum : (Lroot c (m + 1) (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))) ^ 2
          = Lroot c m (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ)) :=
        Lroot_succ_sq c m (exp_add_im_mem ht (hPsim (s : ℝ)))
      have hden : (Lroot c (m + 1) t) ^ 2 = Lroot c m t := Lroot_succ_sq c m ht
      rw [div_pow, hnum, hden]
    have hfin : (1 : ℤ) = 2 * degZ ⟦q1⟧ := by rw [← hq0mdeg, ← hsqeq, degZ_sqLoop]
    omega
  · exact h

/-- **The level-`n` period is exactly `2^n·2πi`.** -/
theorem Lroot_period (n : ℕ) {t : ℂ} (ht : t ∈ coverPlane c) :
    Lroot c n (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = Lroot c n t := by
  induction n generalizing t with
  | zero =>
    rw [Lroot_zero, Lroot_zero]
    have : ((2 ^ 0 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, exp_add_two_pi]
  | succ m ih =>
    have ht' : t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ∈ coverPlane c :=
      exp_add_im_mem ht (vshift_re_zero m)
    have hshift : t + ((2 ^ (m + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = (t + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
          + ((2 ^ m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have h2 : ((2 ^ (m + 1) : ℕ) : ℂ) = ((2 ^ m : ℕ) : ℂ) + ((2 ^ m : ℕ) : ℂ) := by
        push_cast [pow_succ]; ring
      rw [h2]; ring
    rw [hshift, Lroot_flip_of_period m (fun {u} hu => ih hu) ht',
      Lroot_flip_of_period m (fun {u} hu => ih hu) ht, neg_neg]

/-- The `ρ_n` tower never vanishes on the covering half-plane in the connected case. -/
theorem rho_ne_zero (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) : rho c n t ≠ 0 := by
  induction n with
  | zero =>
      simp [rho_zero, Complex.exp_ne_zero]
  | succ n _ =>
      intro hzero
      have hq := quadratic_rho_succ c hc n ht
      rw [hzero] at hq
      simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at hq
      have hmem : rho c n t ∈ escapeLevel c n := rho_mem_escapeLevel c hc n ht
      rw [← hq] at hmem
      exact hc n hmem

/-- **The `ρ_n` tower has dyadic period `2^n·2πi`.** This is the period half of the exact-fiber
theorem still needed for the connected `π₁` computation. The induction step uses that
`ρ_{n+1}(u+P_n)/ρ_{n+1}(u)` is a continuous square-root-of-unity-valued function on the connected
half-plane, hence constant; applying the same constant twice over `2P_n = P_{n+1}` gives period. -/
theorem rho_period (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) :
    rho c n (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = rho c n t := by
  induction n generalizing t with
  | zero =>
      rw [rho_zero, exp_add_pow_period]
  | succ n ih =>
      set P : ℂ := ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) with hPdef
      have hPre : P.re = 0 := by
        rw [hPdef]
        exact vshift_re_zero n
      have htP : t + P ∈ coverPlane c := exp_add_im_mem ht hPre
      have hshift :
          t + ((2 ^ (n + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
            = (t + P) + P := by
        rw [hPdef]
        have h2 : ((2 ^ (n + 1) : ℕ) : ℂ)
            = ((2 ^ n : ℕ) : ℂ) + ((2 ^ n : ℕ) : ℂ) := by
          push_cast [pow_succ]
          ring
        rw [h2]
        ring
      set ξ : ℂ → ℂ := fun u => rho c (n + 1) (u + P) / rho c (n + 1) u with hξdef
      have hξc : ContinuousOn ξ (coverPlane c) := by
        have hnum : ContinuousOn (fun u => rho c (n + 1) (u + P)) (coverPlane c) :=
          (rho_analytic c hc (n + 1)).continuousOn.comp
            ((continuous_id.add continuous_const).continuousOn)
            (fun u hu => by
              change Complex.exp (u + P) ∈ escapeOpen c
              exact exp_add_im_mem hu hPre)
        have hden : ContinuousOn (fun u => rho c (n + 1) u) (coverPlane c) :=
          (rho_analytic c hc (n + 1)).continuousOn
        exact hnum.div hden (fun u hu => rho_ne_zero hc (n + 1) hu)
      have hpow : ∀ u ∈ coverPlane c, ξ u ^ 2 = 1 := by
        intro u hu
        have huP : u + P ∈ coverPlane c := exp_add_im_mem hu hPre
        have hsqP := rho_succ_sq c hc n huP
        have hsq := rho_succ_sq c hc n hu
        have hper : rho c n (u + P) = rho c n u := by
          rw [hPdef]
          exact ih hu
        rw [hξdef, div_pow, hsqP, hsq, hper, div_self]
        exact sub_ne_zero.mpr (fun heq => hc n (by
          have hmem : rho c n u ∈ escapeLevel c n := rho_mem_escapeLevel c hc n hu
          rwa [heq] at hmem))
      have hconst : ξ (t + P) = ξ t :=
        const_of_pow_eq_one (convex_preimage_exp_escapeOpen c).isPreconnected hξc
          (by norm_num : 0 < 2) hpow htP ht
      have hstep_t : rho c (n + 1) (t + P) = ξ t * rho c (n + 1) t := by
        rw [hξdef]
        field_simp [rho_ne_zero hc (n + 1) ht]
      have hstep_tP : rho c (n + 1) ((t + P) + P) =
          ξ (t + P) * rho c (n + 1) (t + P) := by
        rw [hξdef]
        field_simp [rho_ne_zero hc (n + 1) htP]
      have hξsq : ξ t ^ 2 = 1 := hpow t ht
      rw [hshift, hstep_tP, hconst, hstep_t]
      calc
        ξ t * (ξ t * rho c (n + 1) t) = (ξ t) ^ 2 * rho c (n + 1) t := by ring
        _ = rho c (n + 1) t := by rw [hξsq]; ring

/-- The normalized loop traced by `rho_n(t + 2^n 2πi s) - c`. This is the exact
loop whose odd winding forces the next `rho` square-root sheet to swap. -/
noncomputable def rhoShiftLoop (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) : Path one_cs one_cs := by
  let P : ℂ := ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  have hPre : P.re = 0 := by
    dsimp [P]
    exact vshift_re_zero n
  have hPsim : ∀ s : ℝ, (P * (s : ℂ)).re = 0 := by
    intro s
    rw [Complex.mul_re, hPre, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  have hden : rho c n t - c ≠ 0 := by
    intro hzero
    have hmem : rho c n t ∈ escapeLevel c n := rho_mem_escapeLevel c hc n ht
    have heq : rho c n t = c := sub_eq_zero.mp hzero
    rw [heq] at hmem
    exact hc n hmem
  have hnum : ∀ s : I, rho c n (t + P * (s : ℂ)) - c ≠ 0 := by
    intro s hzero
    have hs : t + P * (s : ℂ) ∈ coverPlane c := exp_add_im_mem ht (hPsim (s : ℝ))
    have hmem : rho c n (t + P * (s : ℂ)) ∈ escapeLevel c n := rho_mem_escapeLevel c hc n hs
    have heq : rho c n (t + P * (s : ℂ)) = c := sub_eq_zero.mp hzero
    rw [heq] at hmem
    exact hc n hmem
  have hcont : Continuous fun s : I =>
      (⟨(rho c n (t + P * (s : ℂ)) - c) / (rho c n t - c),
        div_ne_zero (hnum s) hden⟩ : Cs) := by
    have harg : Continuous fun s : I => t + P * (s : ℂ) := by fun_prop
    have hρ : Continuous fun s : I => rho c n (t + P * (s : ℂ)) :=
      (rho_analytic c hc n).continuousOn.comp_continuous harg
        (fun s => exp_add_im_mem ht (hPsim (s : ℝ)))
    exact ((hρ.sub continuous_const).div_const _).subtype_mk _
  exact
    { toFun := fun s =>
        ⟨(rho c n (t + P * (s : ℂ)) - c) / (rho c n t - c), div_ne_zero (hnum s) hden⟩
      continuous_toFun := hcont
      source' := by
        apply Subtype.ext
        show (rho c n (t + P * ((0 : I) : ℂ)) - c) / (rho c n t - c) = (1 : ℂ)
        simp [div_self hden]
      target' := by
        apply Subtype.ext
        show (rho c n (t + P * ((1 : I) : ℂ)) - c) / (rho c n t - c) = (1 : ℂ)
        have hper : rho c n (t + P) = rho c n t := by
          dsimp [P]
          exact rho_period hc n ht
        simp [hper, div_self hden] }

/-- Odd winding of the `rho_n - c` half-period loop forces the next square-root lift to
swap sheets. This is the all-level `rho` analogue of `rho_one_anti`, with the paper's
remaining topological-degree assertion exposed as the `hodd` hypothesis. -/
theorem rho_antiperiod_of_odd_shift_winding (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ)
    {t : ℂ} (ht : t ∈ coverPlane c)
    (hodd : ∃ k : ℤ, degZ ⟦rhoShiftLoop c hc n ht⟧ = 2 * k + 1) :
    rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      -rho c (n + 1) t := by
  let P : ℂ := ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  have hPre : P.re = 0 := by
    dsimp [P]
    exact vshift_re_zero n
  have hPsim : ∀ s : ℝ, (P * (s : ℂ)).re = 0 := by
    intro s
    rw [Complex.mul_re, hPre, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  have htP : t + P ∈ coverPlane c := exp_add_im_mem ht hPre
  have e1 : (rho c (n + 1) (t + P)) ^ 2 = rho c n (t + P) - c :=
    rho_succ_sq c hc n htP
  have e2 : (rho c (n + 1) t) ^ 2 = rho c n t - c := rho_succ_sq c hc n ht
  have hper : rho c n (t + P) = rho c n t := by
    dsimp [P] at htP ⊢
    exact rho_period hc n ht
  have hsq : (rho c (n + 1) (t + P)) ^ 2 = (rho c (n + 1) t) ^ 2 := by
    rw [e1, e2, hper]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsame | hneg
  · exfalso
    have hρne : ∀ s : I, rho c (n + 1) (t + P * (s : ℂ)) ≠ 0 := by
      intro s
      exact rho_ne_zero hc (n + 1) (exp_add_im_mem ht (hPsim (s : ℝ)))
    have hρtne : rho c (n + 1) t ≠ 0 := rho_ne_zero hc (n + 1) ht
    have hcont : Continuous fun s : I =>
        (⟨rho c (n + 1) (t + P * (s : ℂ)) / rho c (n + 1) t,
          div_ne_zero (hρne s) hρtne⟩ : Cs) := by
      have harg : Continuous fun s : I => t + P * (s : ℂ) := by fun_prop
      have hρ : Continuous fun s : I => rho c (n + 1) (t + P * (s : ℂ)) :=
        (rho_analytic c hc (n + 1)).continuousOn.comp_continuous harg
          (fun s => exp_add_im_mem ht (hPsim (s : ℝ)))
      exact (hρ.div_const _).subtype_mk _
    let q1 : Path one_cs one_cs :=
      { toFun := fun s =>
          ⟨rho c (n + 1) (t + P * (s : ℂ)) / rho c (n + 1) t,
            div_ne_zero (hρne s) hρtne⟩
        continuous_toFun := hcont
        source' := by
          apply Subtype.ext
          show rho c (n + 1) (t + P * ((0 : I) : ℂ)) / rho c (n + 1) t = (1 : ℂ)
          simp [div_self hρtne]
        target' := by
          apply Subtype.ext
          show rho c (n + 1) (t + P * ((1 : I) : ℂ)) / rho c (n + 1) t = (1 : ℂ)
          simp [hsame, div_self hρtne] }
    have hsqeq : sqLoop q1 = rhoShiftLoop c hc n ht := by
      apply Path.ext
      funext s
      apply Subtype.ext
      show (rho c (n + 1) (t + P * (s : ℂ)) / rho c (n + 1) t) ^ 2 =
        (rho c n (t + P * (s : ℂ)) - c) / (rho c n t - c)
      have hs : t + P * (s : ℂ) ∈ coverPlane c := exp_add_im_mem ht (hPsim (s : ℝ))
      have hnum : (rho c (n + 1) (t + P * (s : ℂ))) ^ 2 =
          rho c n (t + P * (s : ℂ)) - c := rho_succ_sq c hc n hs
      have hden : (rho c (n + 1) t) ^ 2 = rho c n t - c := rho_succ_sq c hc n ht
      rw [div_pow, hnum, hden]
    obtain ⟨k, hk⟩ := hodd
    have hfin : degZ ⟦rhoShiftLoop c hc n ht⟧ = 2 * degZ ⟦q1⟧ := by
      rw [← hsqeq, degZ_sqLoop]
    omega
  · simpa [P] using hneg

/-- The all-level sheet-swap follows from the concrete odd-winding statement for the
`rho_n - c` half-period loops. This packages the remaining connected topological-degree
claim in the exact shape consumed downstream by the `ρ`-covering route. -/
theorem rho_antiperiod_of_odd_shift_winding_all (hc : ∀ n, c ∉ escapeLevel c n)
    (hodd : ∀ n : ℕ, ∀ {t : ℂ}, ∀ ht : t ∈ coverPlane c,
      ∃ k : ℤ, degZ ⟦rhoShiftLoop c hc n ht⟧ = 2 * k + 1) :
    ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t := by
  intro n t ht
  exact rho_antiperiod_of_odd_shift_winding (c := c) hc n ht (hodd n ht)

/-- Purely-imaginary translation preserves the covering half-plane exactly. -/
theorem add_im_mem_coverPlane_iff {t w : ℂ} (hw : w.re = 0) :
    t + w ∈ coverPlane c ↔ t ∈ coverPlane c := by
  change Complex.exp (t + w) ∈ escapeOpen c ↔ Complex.exp t ∈ escapeOpen c
  have hmod : ‖Complex.exp (t + w)‖ = ‖Complex.exp t‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]
    simp [Complex.add_re, hw]
  simp only [escapeOpen, Set.mem_setOf_eq]
  rw [hmod]

/-- **The `ρ_n` period holds for every integer multiple of `2^n·2πi`.** This converts the fundamental
period theorem into the endpoint-lattice form needed by the exact-fiber induction. -/
theorem rho_period_int_mul (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) (k : ℤ) {t : ℂ}
    (ht : t ∈ coverPlane c) :
    rho c n (t + (k : ℂ) * (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)))
      = rho c n t := by
  classical
  set P : ℂ := ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) with hPdef
  have hPre : P.re = 0 := by
    rw [hPdef]
    exact vshift_re_zero n
  have hkPre : ((k : ℂ) * P).re = 0 := by
    simp [Complex.mul_re, hPre]
  let R : ℂ → ℂ := fun z => if hz : z ∈ coverPlane c then rho c n z else 0
  have hper : Function.Periodic R P := by
    intro z
    by_cases hz : z ∈ coverPlane c
    · have hzP : z + P ∈ coverPlane c := (add_im_mem_coverPlane_iff hPre).mpr hz
      dsimp [R]
      rw [if_pos hzP, if_pos hz, hPdef]
      exact rho_period hc n hz
    · have hzP : z + P ∉ coverPlane c := fun hzP => hz ((add_im_mem_coverPlane_iff hPre).mp hzP)
      dsimp [R]
      rw [if_neg hzP, if_neg hz]
  have htshift : t + (k : ℂ) * P ∈ coverPlane c := (add_im_mem_coverPlane_iff hkPre).mpr ht
  have h := (hper.int_mul k) t
  dsimp [R] at h
  rw [if_pos htshift, if_pos ht] at h
  simpa [P] using h

/-- If `ρ_{n+1}` swaps sheets over the half-period `2^n·2πi`, then every odd multiple of that
half-period also swaps sheets. -/
theorem rho_antiperiod_odd_int_mul (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (n : ℕ) (j : ℤ) {t : ℂ} (ht : t ∈ coverPlane c) :
    rho c (n + 1)
        (t + (((2 : ℤ) ^ n * (2 * j + 1) : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I))
      = -rho c (n + 1) t := by
  set T : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hTdef
  set P : ℂ := ((2 ^ n : ℕ) : ℂ) * T with hPdef
  have hPre : P.re = 0 := by
    rw [hPdef, hTdef]
    exact vshift_re_zero n
  have htP : t + P ∈ coverPlane c := (add_im_mem_coverPlane_iff hPre).mpr ht
  have hshift :
      t + (((2 : ℤ) ^ n * (2 * j + 1) : ℤ) : ℂ) * T
        = (t + P) + (j : ℂ) * (((2 ^ (n + 1) : ℕ) : ℂ) * T) := by
    rw [hPdef]
    push_cast
    rw [pow_succ]
    ring
  rw [hshift]
  rw [rho_period_int_mul (c := c) hc (n + 1) j htP]
  rw [hPdef, hTdef] at htP
  rw [hPdef, hTdef]
  exact hanti n ht

/-- **Exact `ρ_n` fibers from the one-step sheet swap.** If the tower has the genuine deck-swap
`ρ_{n+1}(t+2^n·2πi) = -ρ_{n+1}(t)` at every level, then equality in a `ρ_n` fiber forces the
endpoint displacement to lie in the dyadic period lattice `2^n·2πi·ℤ`. This is the algebraic induction
behind the remaining connected `π₁` theorem. -/
theorem rho_fiber_dyadic_of_antiperiod (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (n : ℕ) {t t' : ℂ} (ht : t ∈ coverPlane c) (ht' : t' ∈ coverPlane c)
    (h : rho c n t = rho c n t') :
    ∃ k : ℤ, t - t' =
      (((2 : ℤ) ^ n * k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  induction n generalizing t t' with
  | zero =>
      have he : Complex.exp t = Complex.exp t' := by
        simpa [rho_zero] using h
      rw [Complex.exp_eq_exp_iff_exists_int] at he
      obtain ⟨k, hk⟩ := he
      refine ⟨k, ?_⟩
      rw [hk]
      ring_nf
  | succ n ih =>
      have hbase : rho c n t = rho c n t' := by
        calc
          rho c n t = quadratic c (rho c (n + 1) t) := (quadratic_rho_succ c hc n ht).symm
          _ = quadratic c (rho c (n + 1) t') := by rw [h]
          _ = rho c n t' := quadratic_rho_succ c hc n ht'
      obtain ⟨k, hk⟩ := ih ht ht' hbase
      rcases Int.even_or_odd k with hkEven | hkOdd
      · rcases hkEven with ⟨j, hj⟩
        refine ⟨j, ?_⟩
        calc
          t - t' = (((2 : ℤ) ^ n * k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
          _ = (((2 : ℤ) ^ (n + 1) * j : ℤ) : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I) := by
                rw [hj]
                push_cast
                rw [pow_succ]
                ring
      · rcases hkOdd with ⟨j, hj⟩
        exfalso
        have hodd :
            t - t' = (((2 : ℤ) ^ n * (2 * j + 1) : ℤ) : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I) := by
          rw [hj] at hk
          exact hk
        have ht_eq :
            t = t' + (((2 : ℤ) ^ n * (2 * j + 1) : ℤ) : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I) := by
          linear_combination hodd
        have hswap := rho_antiperiod_odd_int_mul (c := c) hc hanti n j ht'
        rw [← ht_eq] at hswap
        rw [h] at hswap
        have hzero : rho c (n + 1) t' = 0 := by
          have htwo : (2 : ℂ) * rho c (n + 1) t' = 0 := by
            linear_combination hswap
          exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
        exact (rho_ne_zero hc (n + 1) ht') hzero

/-- The dyadic vertical period `2^n·2πi` is nonzero. -/
theorem dyadic_period_ne_zero (n : ℕ) :
    ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · norm_num
  · exact Complex.two_pi_I_ne_zero

/-- Reassociate the integer coefficient in the dyadic period lattice. -/
theorem int_two_pow_mul_period_eq_int_mul_dyadic_period (n : ℕ) (k : ℤ) :
    ((((2 : ℤ) ^ n * k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      (k : ℂ) * (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
  push_cast
  ring

/-- Integer multiples of the nonzero dyadic period cancel. -/
theorem int_mul_dyadic_period_cancel (n : ℕ) {k l : ℤ}
    (h : (k : ℂ) * (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      (l : ℂ) * (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) :
    k = l := by
  have hk : (k : ℂ) = (l : ℂ) := mul_right_cancel₀ (dyadic_period_ne_zero n) h
  exact_mod_cast hk

/-- **Exact `ρ_n` fibers as deck translations.** This is the additive form of
`rho_fiber_dyadic_of_antiperiod`: two points in the same `ρ_n` fiber differ by an integer multiple of
the dyadic period `2^n·2πi`. This is the form needed to assemble evenly-covered neighborhoods for the
explicit `ρ_n` maps. -/
theorem rho_fiber_eq_add_dyadic_period_of_antiperiod (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (n : ℕ) {t t' : ℂ} (ht : t ∈ coverPlane c) (ht' : t' ∈ coverPlane c)
    (h : rho c n t = rho c n t') :
    ∃ k : ℤ, t = t' + (k : ℂ) * (((2 ^ n : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I)) := by
  obtain ⟨k, hk⟩ := rho_fiber_dyadic_of_antiperiod (c := c) hc hanti n ht ht' h
  refine ⟨k, ?_⟩
  rw [int_two_pow_mul_period_eq_int_mul_dyadic_period n k] at hk
  linear_combination hk

/-- **Exact `ρ_n` fibers from odd half-period winding, as deck translations.** The proof-shaped
odd-winding input first gives the sheet swap, then the exact fiber theorem gives the dyadic deck
translation. -/
theorem rho_fiber_eq_add_dyadic_period_of_odd_shift_winding (hc : ∀ n, c ∉ escapeLevel c n)
    (hodd : ∀ n : ℕ, ∀ {t : ℂ}, ∀ ht : t ∈ coverPlane c,
      ∃ k : ℤ, degZ ⟦rhoShiftLoop c hc n ht⟧ = 2 * k + 1)
    (n : ℕ) {t t' : ℂ} (ht : t ∈ coverPlane c) (ht' : t' ∈ coverPlane c)
    (h : rho c n t = rho c n t') :
    ∃ k : ℤ, t = t' + (k : ℂ) * (((2 ^ n : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I)) :=
  rho_fiber_eq_add_dyadic_period_of_antiperiod (c := c) hc
    (rho_antiperiod_of_odd_shift_winding_all (c := c) hc hodd) n ht ht' h

/-- **Weak fiber containment: `ρ_n`-fibers sit inside the `exp`-fibers `2πiℤ`.** Since
`f^[n] ∘ ρ_n = exp` on `H` (`iterate_quadratic_rho`), `ρ_n t = ρ_n t'` forces `exp t = exp t'`, hence
`t − t' ∈ 2πiℤ`. This is the easy half of the fiber structure; the `2ⁿ`-refinement (`t − t' ∈ 2ⁿ·2πiℤ`)
is the genuine remaining content, governed by the connectedness of the filled Julia set. -/
theorem rho_fiber_sub_2pi (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t t' : ℂ}
    (ht : t ∈ coverPlane c) (ht' : t' ∈ coverPlane c) (h : rho c n t = rho c n t') :
    ∃ k : ℤ, t - t' = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have he : Complex.exp t = Complex.exp t' := by
    rw [← iterate_quadratic_rho c hc n ht, ← iterate_quadratic_rho c hc n ht', h]
  rw [Complex.exp_eq_exp_iff_exists_int] at he
  obtain ⟨k, hk⟩ := he
  exact ⟨k, by rw [hk]; ring⟩

end Bottcher
