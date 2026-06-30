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
      have hd := degZ_powLoop (2 ^ m) q0m
      rw [hpow, hq0deg] at hd
      have h2m : ((2 ^ m : ℕ) : ℤ) ≠ 0 := by positivity
      have heq : ((2 ^ m : ℕ) : ℤ) * 1 = ((2 ^ m : ℕ) : ℤ) * degZ ⟦q0m⟧ := by rw [mul_one]; exact hd
      exact (mul_left_cancel₀ h2m heq).symm
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

end Bottcher
