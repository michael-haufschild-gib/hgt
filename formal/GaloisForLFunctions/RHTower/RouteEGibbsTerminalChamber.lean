import GaloisForLFunctions.RHTower.PrimeWindowLawNoLog
import GaloisForLFunctions.RHTower.GibbsAntiscaleDeterminantOddCube

/-!
# The terminal antiscale chamber of the critical Euler determinant

At the terminal frequency `t_X = π/log X` every prime of the chamber `X/e < p ≤ X` has phase in
`[π - π/log X, π]`, so its critical transverse coordinate `u_p = 2d_p cos(t_X log p)` is negative
with `|u_p| ≥ d_p`, where `d_p = p^{-1/2}/(1+p^{-1})` is the critical half density.  Every odd
grade of the Euler determinant therefore reinforces, and

```text
log(1 + | |Z_P(1/2+it_X)|² - |M_P(1/2+it_X)|² | ) ≍ √X / log X,
```

because the chamber mass `∑_{X/e<p≤X} p^{-1/2}` is `(2 - 2e^{-1/2})√X/log X (1+o(1))` by the
prime window law.  Thus the terminal chamber is spectrally transverse on the exponential scale.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## The chamber -/

/-- The terminal antiscale chamber `{p prime : X/e < p ≤ X}`. -/
def terminalChamber (X : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊X / Real.exp 1⌋₊ ⌊X⌋₊).filter Nat.Prime

/-- The terminal antiscale frequency `t_X = π/log X`. -/
def terminalFrequency (X : ℝ) : ℝ := Real.pi / Real.log X

/-- The reciprocal square-root mass of the chamber. -/
def chamberMass (X : ℝ) : ℝ := ∑ p ∈ terminalChamber X, (p : ℝ) ^ (-(1 : ℝ) / 2)

theorem mem_terminalChamber {X : ℝ} (hX : 0 < X) {p : ℕ} (hp : p ∈ terminalChamber X) :
    p.Prime ∧ X / Real.exp 1 < (p : ℝ) ∧ (p : ℝ) ≤ X := by
  rw [terminalChamber, Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hlow, hhigh⟩, hprime⟩ := hp
  refine ⟨hprime, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have : p ≤ ⌊X / Real.exp 1⌋₊ := Nat.le_floor hcon
    omega
  · have h : (p : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hhigh
    exact le_trans h (Nat.floor_le hX.le)

/-! ## The phase of the chamber -/

theorem terminalChamber_phase_le_pi {X : ℝ} (hX : 1 < X) {p : ℕ} (hp : p ∈ terminalChamber X) :
    terminalFrequency X * Real.log p ≤ Real.pi := by
  obtain ⟨hprime, _, hple⟩ := mem_terminalChamber (by linarith) hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos hX
  have hlogp : Real.log p ≤ Real.log X := Real.log_le_log hp0 hple
  rw [terminalFrequency, div_mul_eq_mul_div, div_le_iff₀ hlogX]
  nlinarith [Real.pi_pos, hlogp]

theorem terminalChamber_pi_sub_le_phase {X : ℝ} (hX : 1 < X) {p : ℕ}
    (hp : p ∈ terminalChamber X) :
    Real.pi - Real.pi / Real.log X ≤ terminalFrequency X * Real.log p := by
  obtain ⟨hprime, hlow, _⟩ := mem_terminalChamber (by linarith) hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogdiv : Real.log (X / Real.exp 1) = Real.log X - 1 := by
    rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  have hlogp : Real.log X - 1 ≤ Real.log p := by
    have hpos : (0 : ℝ) < X / Real.exp 1 := by positivity
    have h := Real.log_le_log hpos hlow.le
    rwa [hlogdiv] at h
  rw [terminalFrequency, div_mul_eq_mul_div, le_div_iff₀ hlogX]
  have hπ := Real.pi_pos
  have hkey : (Real.pi - Real.pi / Real.log X) * Real.log X = Real.pi * Real.log X - Real.pi := by
    field_simp
  rw [hkey]
  nlinarith [hlogp, hπ]

/-- Past `e³` every chamber phase lies in `[2π/3, π]`, so its cosine is at most `-1/2`. -/
theorem cos_terminalChamber_le {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ}
    (hp : p ∈ terminalChamber X) :
    Real.cos (terminalFrequency X * Real.log p) ≤ -(1 / 2) := by
  have hX1 : (1 : ℝ) < X := by
    have h3 : (1 : ℝ) < Real.exp 3 := by
      have := Real.exp_pos 3
      have h := Real.add_one_le_exp (3 : ℝ)
      linarith
    linarith
  have hlogX : (3 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 3) hX
    rwa [Real.log_exp] at h
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hupper := terminalChamber_phase_le_pi hX1 hp
  have hlower := terminalChamber_pi_sub_le_phase hX1 hp
  have hπ := Real.pi_pos
  have hbase : 2 * Real.pi / 3 ≤ terminalFrequency X * Real.log p := by
    have hdiv : Real.pi / Real.log X ≤ Real.pi / 3 :=
      div_le_div_of_nonneg_left hπ.le (by norm_num) hlogX
    linarith
  have hcos23 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    have h : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  calc Real.cos (terminalFrequency X * Real.log p) ≤ Real.cos (2 * Real.pi / 3) := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hupper hbase
    _ = -(1 / 2) := hcos23

/-! ## The chamber mass -/

theorem chamberMass_eq_sub {X : ℝ} (hX : Real.exp 3 ≤ X) :
    chamberMass X =
      primeWindowSumNoLog (1 / 2) 0 X - primeWindowSumNoLog (1 / 2) 0 (X / Real.exp 1) := by
  have hX1 : (1 : ℝ) < X := by
    have h3 : (1 : ℝ) < Real.exp 3 := by
      have h := Real.add_one_le_exp (3 : ℝ)
      linarith
    linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hexp3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have he1 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have hdiv4 : (4 : ℝ) ≤ X / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]
    have hle : Real.exp 1 * Real.exp 1 * Real.exp 1 ≤ X := by
      rw [← hexp3]
      exact hX
    nlinarith [Real.exp_pos 1, he1]
  have hfloorlow : 2 ≤ ⌊X / Real.exp 1⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2:ℝ) ≤ X / Real.exp 1))
  have hdivle : X / Real.exp 1 ≤ X := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_pos 1, he1]
  have hfloorle : ⌊X / Real.exp 1⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hdivle
  have hsplit := Finset.sum_Ioc_consecutive
    (fun k : ℕ => (if k.Prime then ((k : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - 1) *
      (Real.log X - Real.log k) ^ 0 else 0)) hfloorlow hfloorle
  have hsplit2 := Finset.sum_Ioc_consecutive
    (fun k : ℕ => (if k.Prime then ((k : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - 1) *
      (Real.log (X / Real.exp 1) - Real.log k) ^ 0 else 0)) hfloorlow hfloorle
  have hlow : primeWindowSumNoLog (1 / 2) 0 (X / Real.exp 1)
      = ∑ k ∈ Finset.Ioc 2 ⌊X / Real.exp 1⌋₊,
        (if k.Prime then ((k : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - 1) *
          (Real.log X - Real.log k) ^ 0 else 0) := by
    rw [primeWindowSumNoLog]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime <;> simp [hp]
  have hfull : primeWindowSumNoLog (1 / 2) 0 X
      = ∑ k ∈ Finset.Ioc 2 ⌊X⌋₊,
        (if k.Prime then ((k : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - 1) *
          (Real.log X - Real.log k) ^ 0 else 0) := rfl
  rw [hfull, hlow, ← hsplit]
  have hchamber : chamberMass X
      = ∑ k ∈ Finset.Ioc ⌊X / Real.exp 1⌋₊ ⌊X⌋₊,
        (if k.Prime then ((k : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - 1) *
          (Real.log X - Real.log k) ^ 0 else 0) := by
    rw [chamberMass, terminalChamber, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp, pow_zero, mul_one]
      congr 1
      norm_num
    · rw [if_neg hp, if_neg hp]
  rw [hchamber]
  ring

/-- **The chamber mass.**  `∑_{X/e<p≤X} p^{-1/2} = (2 - 2e^{-1/2})√X/log X (1 + o(1))`. -/
theorem tendsto_chamberMass :
    Tendsto (fun X : ℝ => chamberMass X * Real.log X / X ^ ((1 : ℝ) / 2)) atTop
      (nhds (2 - 2 * Real.exp (-(1 : ℝ) / 2))) := by
  have ha0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hfull := tendsto_logY_mul_primeWindowSumNoLog ha0 0
  have hconst : (Nat.factorial 0 : ℝ) / ((1 : ℝ) / 2) ^ (0 + 1) = 2 := by
    simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    norm_num
  rw [hconst] at hfull
  -- the shifted copy
  have hshift : Tendsto (fun X : ℝ => X / Real.exp 1) atTop atTop := by
    have h := Filter.tendsto_id (x := (atTop : Filter ℝ))
    exact Filter.Tendsto.atTop_div_const (Real.exp_pos 1) h
  have hlow := hfull.comp hshift
  have hlogratio : Tendsto (fun X : ℝ => Real.log X / (Real.log X - 1)) atTop (nhds 1) := by
    have hone : Tendsto (fun X : ℝ => 1 - 1 / Real.log X) atTop (nhds 1) := by
      have h : Tendsto (fun X : ℝ => (1 : ℝ) / Real.log X) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
      have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub h
      rwa [sub_zero] at h2
    have hinv := hone.inv₀ (by norm_num)
    rw [inv_one] at hinv
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with X hX
    have hlogpos : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
    have hlogne : Real.log X ≠ 0 := ne_of_gt hlogpos
    have h1 : (1 : ℝ) - 1 / Real.log X = (Real.log X - 1) / Real.log X := by
      field_simp
    rw [h1, inv_div]
  -- assemble
  have hlowfinal : Tendsto
      (fun X : ℝ => primeWindowSumNoLog (1 / 2) 0 (X / Real.exp 1) * Real.log X /
        X ^ ((1 : ℝ) / 2)) atTop (nhds (2 * Real.exp (-(1 : ℝ) / 2))) := by
    have hprod := hlow.mul hlogratio
    rw [mul_one] at hprod
    have hscale : Tendsto (fun X : ℝ =>
        (Real.log (X / Real.exp 1) * primeWindowSumNoLog (1 / 2) 0 (X / Real.exp 1) /
          (X / Real.exp 1) ^ ((1 : ℝ) / 2)) * (Real.log X / (Real.log X - 1))) atTop
        (nhds 2) := hprod
    have hfinal := hscale.const_mul (Real.exp (-(1 : ℝ) / 2))
    rw [show Real.exp (-(1 : ℝ) / 2) * 2 = 2 * Real.exp (-(1 : ℝ) / 2) from by ring] at hfinal
    refine hfinal.congr' ?_
    filter_upwards [eventually_ge_atTop (Real.exp 3)] with X hX
    have h3 : (1 : ℝ) < Real.exp 3 := by
      have h := Real.add_one_le_exp (3 : ℝ)
      linarith
    have hX1 : (1 : ℝ) < X := by linarith
    have hXpos : (0 : ℝ) < X := by linarith
    have hlogX : (0 : ℝ) < Real.log X := Real.log_pos hX1
    have hlogdiv : Real.log (X / Real.exp 1) = Real.log X - 1 := by
      rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
    have hlogX3 : (3 : ℝ) ≤ Real.log X := by
      have h := Real.log_le_log (Real.exp_pos 3) hX
      rwa [Real.log_exp] at h
    have hlogne : Real.log X - 1 ≠ 0 := by linarith
    have hrpow : (X / Real.exp 1) ^ ((1 : ℝ) / 2)
        = X ^ ((1 : ℝ) / 2) * Real.exp (-(1 : ℝ) / 2) := by
      rw [Real.div_rpow hXpos.le (Real.exp_pos 1).le, Real.exp_one_rpow, div_eq_mul_inv,
        ← Real.exp_neg]
      norm_num
    have hXhalf : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hXpos _
    have hexpne : Real.exp (-(1 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    rw [hlogdiv, hrpow]
    field_simp
  have hsum := hfull.sub hlowfinal
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.exp 3)] with X hX
  rw [chamberMass_eq_sub hX]
  ring

/-! ## The chamber determinant -/

/-- The critical Euler radius `p^{-1/2}`. -/
def chamberRadius (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 : ℝ) / 2)

/-- The positive drag `-u_p` of one chamber prime. -/
def chamberDrag (X : ℝ) (p : ℕ) : ℝ :=
  -(2 * chamberRadius p * Real.cos (terminalFrequency X * Real.log p) /
    (1 + chamberRadius p ^ 2))

/-- The chamber determinant `|Z_P(1/2+it_X)|² - |M_P(1/2+it_X)|²`. -/
def chamberDeterminant (X : ℝ) : ℝ :=
  (∏ p ∈ terminalChamber X, Complex.normSq
      (1 + ((chamberRadius p : ℝ) : ℂ) *
        Complex.exp (((-(terminalFrequency X * Real.log p) : ℝ) : ℂ) * Complex.I)))
    - ∏ p ∈ terminalChamber X, Complex.normSq
      (1 - ((chamberRadius p : ℝ) : ℂ) *
        Complex.exp (((-(terminalFrequency X * Real.log p) : ℝ) : ℂ) * Complex.I))

theorem chamberRadius_pos {p : ℕ} (hp : p.Prime) : 0 < chamberRadius p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  exact Real.rpow_pos_of_pos hp0 _

theorem chamberRadius_sq_le {p : ℕ} (hp : p.Prime) : chamberRadius p ^ 2 ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsq : chamberRadius p ^ 2 = (p : ℝ)⁻¹ := by
    rw [chamberRadius, ← Real.rpow_natCast (((p : ℝ)) ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hp0.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hsq, inv_le_comm₀ hp0 (by norm_num)]
  linarith

theorem chamberRadius_lt_one {p : ℕ} (hp : p.Prime) : chamberRadius p < 1 := by
  have h := chamberRadius_sq_le hp
  have hpos := chamberRadius_pos hp
  nlinarith

theorem chamberDrag_eq (X : ℝ) (p : ℕ) :
    chamberDrag X p =
      (-(2 * chamberRadius p * Real.cos (terminalFrequency X * Real.log p))) /
        (1 + chamberRadius p ^ 2) := by
  rw [chamberDrag, neg_div]

/-- Each chamber prime drags by at least its critical half density. -/
theorem chamberDrag_ge {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ} (hp : p ∈ terminalChamber X) :
    chamberRadius p / (1 + chamberRadius p ^ 2) ≤ chamberDrag X p := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr := chamberRadius_pos hprime
  have hden : (0 : ℝ) < 1 + chamberRadius p ^ 2 := by positivity
  have hcos := cos_terminalChamber_le hX hp
  rw [chamberDrag_eq]
  refine div_le_div_of_nonneg_right ?_ hden.le
  nlinarith [hcos, hr]

theorem chamberDrag_le {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ} (hp : p ∈ terminalChamber X) :
    chamberDrag X p ≤ 2 * chamberRadius p / (1 + chamberRadius p ^ 2) := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr := chamberRadius_pos hprime
  have hden : (0 : ℝ) < 1 + chamberRadius p ^ 2 := by positivity
  have hcos : -1 ≤ Real.cos (terminalFrequency X * Real.log p) := Real.neg_one_le_cos _
  rw [chamberDrag_eq]
  refine div_le_div_of_nonneg_right ?_ hden.le
  nlinarith [hcos, hr]

theorem chamberDrag_nonneg {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ} (hp : p ∈ terminalChamber X) :
    0 ≤ chamberDrag X p := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr := chamberRadius_pos hprime
  have hden : (0 : ℝ) < 1 + chamberRadius p ^ 2 := by positivity
  have h := chamberDrag_ge hX hp
  have hpos : (0 : ℝ) < chamberRadius p / (1 + chamberRadius p ^ 2) := by positivity
  linarith

theorem chamberDrag_lt_one {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ} (hp : p ∈ terminalChamber X) :
    chamberDrag X p < 1 := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr := chamberRadius_pos hprime
  have hr1 := chamberRadius_lt_one hprime
  have hden : (0 : ℝ) < 1 + chamberRadius p ^ 2 := by positivity
  have h := chamberDrag_le hX hp
  have hlt : 2 * chamberRadius p / (1 + chamberRadius p ^ 2) < 1 := by
    rw [div_lt_one hden]
    nlinarith [sq_nonneg (1 - chamberRadius p)]
  linarith

theorem chamberDrag_le_two_radius {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ}
    (hp : p ∈ terminalChamber X) : chamberDrag X p ≤ 2 * chamberRadius p := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr := chamberRadius_pos hprime
  have hden : (0 : ℝ) < 1 + chamberRadius p ^ 2 := by positivity
  have h := chamberDrag_le hX hp
  have hle : 2 * chamberRadius p / (1 + chamberRadius p ^ 2) ≤ 2 * chamberRadius p := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (chamberRadius p), hr]
  linarith

theorem chamberDrag_ge_two_thirds {X : ℝ} (hX : Real.exp 3 ≤ X) {p : ℕ}
    (hp : p ∈ terminalChamber X) : 2 * chamberRadius p / 3 ≤ chamberDrag X p := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr := chamberRadius_pos hprime
  have hrsq := chamberRadius_sq_le hprime
  have hden : (0 : ℝ) < 1 + chamberRadius p ^ 2 := by positivity
  have h := chamberDrag_ge hX hp
  have hle : 2 * chamberRadius p / 3 ≤ chamberRadius p / (1 + chamberRadius p ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) hden]
    nlinarith [hr, hrsq]
  linarith

/-- The determinant factors into baseline Euler mass and the transverse drag cube. -/
theorem chamberDeterminant_eq (X : ℝ) :
    chamberDeterminant X
      = (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2)) *
        ((∏ p ∈ terminalChamber X, (1 - chamberDrag X p))
          - ∏ p ∈ terminalChamber X, (1 + chamberDrag X p)) := by
  rw [chamberDeterminant, GibbsGas.prod_normSq_plus_sub_prod_normSq_minus_eq]
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun p _ => ?_
    simp only [GibbsGas.criticalEulerTransverseCoordinate, chamberDrag, Real.cos_neg]
    ring
  · refine Finset.prod_congr rfl fun p _ => ?_
    simp only [GibbsGas.criticalEulerTransverseCoordinate, chamberDrag, Real.cos_neg]
    ring

theorem chamberMass_eq_sum (X : ℝ) :
    chamberMass X = ∑ p ∈ terminalChamber X, chamberRadius p := rfl

theorem chamberMass_nonneg {X : ℝ} (hX : Real.exp 3 ≤ X) : 0 ≤ chamberMass X := by
  rw [chamberMass_eq_sum]
  exact Finset.sum_nonneg fun p hp => (chamberRadius_pos (Finset.mem_filter.mp hp).2).le

/-- **The chamber determinant is exponentially large.** -/
theorem exp_chamberMass_div_three_sub_one_le {X : ℝ} (hX : Real.exp 3 ≤ X) :
    Real.exp (chamberMass X / 3) - 1 ≤ |chamberDeterminant X| := by
  have hbase : (1 : ℝ) ≤ ∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2) := by
    calc (1 : ℝ) = ∏ _p ∈ terminalChamber X, (1 : ℝ) := by simp
      _ ≤ ∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2) :=
        Finset.prod_le_prod (fun p _ => by norm_num)
          (fun p hp => by nlinarith [chamberRadius_pos (Finset.mem_filter.mp hp).2])
  have hbase0 : (0 : ℝ) ≤ ∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2) := by linarith
  have hlow : (∏ p ∈ terminalChamber X, (1 - chamberDrag X p)) ≤ 1 := by
    calc (∏ p ∈ terminalChamber X, (1 - chamberDrag X p))
        ≤ ∏ p ∈ terminalChamber X, (1 : ℝ) :=
          Finset.prod_le_prod (fun p hp => by linarith [chamberDrag_lt_one hX hp])
            (fun p hp => by linarith [chamberDrag_nonneg hX hp])
      _ = 1 := by simp
  have hexp : Real.exp (chamberMass X / 3) ≤ ∏ p ∈ terminalChamber X, (1 + chamberDrag X p) := by
    have hsum : chamberMass X / 3 ≤ ∑ p ∈ terminalChamber X, Real.log (1 + chamberDrag X p) := by
      have hterm : ∀ p ∈ terminalChamber X,
          chamberRadius p / 3 ≤ Real.log (1 + chamberDrag X p) := by
        intro p hp
        have hd0 := chamberDrag_nonneg hX hp
        have hd1 := chamberDrag_lt_one hX hp
        have hd23 := chamberDrag_ge_two_thirds hX hp
        have hpos : (0 : ℝ) < 1 + chamberDrag X p := by linarith
        have hlog : chamberDrag X p / (1 + chamberDrag X p) ≤ Real.log (1 + chamberDrag X p) := by
          have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + chamberDrag X p) by positivity)
          rw [Real.log_div one_ne_zero (ne_of_gt hpos), Real.log_one, zero_sub] at h
          have hval : 1 / (1 + chamberDrag X p) - 1
              = -(chamberDrag X p / (1 + chamberDrag X p)) := by
            rw [div_sub_one (ne_of_gt hpos), ← neg_div]
            congr 1
            ring
          rw [hval] at h
          linarith
        have hhalf : chamberDrag X p / 2 ≤ chamberDrag X p / (1 + chamberDrag X p) := by
          rw [div_le_div_iff₀ (by norm_num) hpos]
          nlinarith [mul_nonneg hd0 (by linarith : (0:ℝ) ≤ 1 - chamberDrag X p)]
        linarith
      rw [chamberMass_eq_sum, Finset.sum_div]
      exact Finset.sum_le_sum hterm
    calc Real.exp (chamberMass X / 3)
        ≤ Real.exp (∑ p ∈ terminalChamber X, Real.log (1 + chamberDrag X p)) :=
          Real.exp_le_exp.mpr hsum
      _ = ∏ p ∈ terminalChamber X, (1 + chamberDrag X p) := by
          rw [Real.exp_sum]
          refine Finset.prod_congr rfl fun p hp => ?_
          exact Real.exp_log (by linarith [chamberDrag_nonneg hX hp])
  have hone : (1 : ℝ) ≤ Real.exp (chamberMass X / 3) :=
    Real.one_le_exp (by linarith [chamberMass_nonneg hX])
  have hdiff : (0 : ℝ) ≤ (∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
      - ∏ p ∈ terminalChamber X, (1 - chamberDrag X p) := by linarith
  have habs : |chamberDeterminant X|
      = (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2)) *
        ((∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
          - ∏ p ∈ terminalChamber X, (1 - chamberDrag X p)) := by
    rw [chamberDeterminant_eq, abs_mul, abs_of_nonneg hbase0, abs_of_nonpos (by linarith)]
    ring
  rw [habs]
  nlinarith [hexp, hlow, hbase, hdiff]

/-- **The chamber determinant is at most exponentially large.** -/
theorem log_one_add_abs_chamberDeterminant_le {X : ℝ} (hX : Real.exp 3 ≤ X) :
    Real.log (1 + |chamberDeterminant X|) ≤ Real.log 2 + 3 * chamberMass X := by
  have hM0 := chamberMass_nonneg hX
  have hbase : (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2))
      ≤ Real.exp (chamberMass X) := by
    have hstep : (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2))
        ≤ ∏ p ∈ terminalChamber X, Real.exp (chamberRadius p) := by
      refine Finset.prod_le_prod (fun p hp => by
        nlinarith [chamberRadius_pos (Finset.mem_filter.mp hp).2]) (fun p hp => ?_)
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hr := chamberRadius_pos hprime
      have hr1 := chamberRadius_lt_one hprime
      have hle : 1 + chamberRadius p ^ 2 ≤ 1 + chamberRadius p := by nlinarith
      have hexp := Real.add_one_le_exp (chamberRadius p)
      linarith
    calc (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2))
        ≤ ∏ p ∈ terminalChamber X, Real.exp (chamberRadius p) := hstep
      _ = Real.exp (chamberMass X) := by rw [← Real.exp_sum, chamberMass_eq_sum]
  have hplus : (∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
      ≤ Real.exp (2 * chamberMass X) := by
    have hstep : (∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
        ≤ ∏ p ∈ terminalChamber X, Real.exp (2 * chamberRadius p) := by
      refine Finset.prod_le_prod (fun p hp => by linarith [chamberDrag_nonneg hX hp])
        (fun p hp => ?_)
      have hle := chamberDrag_le_two_radius hX hp
      have hexp := Real.add_one_le_exp (2 * chamberRadius p)
      linarith
    calc (∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
        ≤ ∏ p ∈ terminalChamber X, Real.exp (2 * chamberRadius p) := hstep
      _ = Real.exp (2 * chamberMass X) := by
          rw [← Real.exp_sum, chamberMass_eq_sum, Finset.mul_sum]
  have hlow : (∏ p ∈ terminalChamber X, (1 - chamberDrag X p)) ≤ 1 := by
    calc (∏ p ∈ terminalChamber X, (1 - chamberDrag X p))
        ≤ ∏ p ∈ terminalChamber X, (1 : ℝ) :=
          Finset.prod_le_prod (fun p hp => by linarith [chamberDrag_lt_one hX hp])
            (fun p hp => by linarith [chamberDrag_nonneg hX hp])
      _ = 1 := by simp
  have hlow0 : (0 : ℝ) ≤ ∏ p ∈ terminalChamber X, (1 - chamberDrag X p) :=
    Finset.prod_nonneg fun p hp => by linarith [chamberDrag_lt_one hX hp]
  have hplus0 : (0 : ℝ) ≤ ∏ p ∈ terminalChamber X, (1 + chamberDrag X p) :=
    Finset.prod_nonneg fun p hp => by linarith [chamberDrag_nonneg hX hp]
  have hbase0 : (0 : ℝ) ≤ ∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2) :=
    Finset.prod_nonneg fun p hp => by
      nlinarith [chamberRadius_pos (Finset.mem_filter.mp hp).2]
  have hdiffnn : (0 : ℝ) ≤ (∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
      - ∏ p ∈ terminalChamber X, (1 - chamberDrag X p) := by
    have hge : (∏ p ∈ terminalChamber X, (1 - chamberDrag X p))
        ≤ ∏ p ∈ terminalChamber X, (1 + chamberDrag X p) :=
      Finset.prod_le_prod (fun p hp => by linarith [chamberDrag_lt_one hX hp])
        (fun p hp => by linarith [chamberDrag_nonneg hX hp])
    linarith
  have habs : |chamberDeterminant X|
      ≤ (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2)) *
        ∏ p ∈ terminalChamber X, (1 + chamberDrag X p) := by
    rw [chamberDeterminant_eq, abs_mul, abs_of_nonneg hbase0]
    refine mul_le_mul_of_nonneg_left ?_ hbase0
    rw [abs_sub_comm, abs_of_nonneg hdiffnn]
    linarith
  have hprod : (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2)) *
      (∏ p ∈ terminalChamber X, (1 + chamberDrag X p)) ≤ Real.exp (3 * chamberMass X) := by
    calc (∏ p ∈ terminalChamber X, (1 + chamberRadius p ^ 2)) *
          (∏ p ∈ terminalChamber X, (1 + chamberDrag X p))
        ≤ Real.exp (chamberMass X) * Real.exp (2 * chamberMass X) :=
          mul_le_mul hbase hplus hplus0 (Real.exp_pos _).le
      _ = Real.exp (3 * chamberMass X) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hfinal : 1 + |chamberDeterminant X| ≤ 2 * Real.exp (3 * chamberMass X) := by
    have hexp1 : (1 : ℝ) ≤ Real.exp (3 * chamberMass X) := Real.one_le_exp (by linarith)
    linarith [habs, hprod]
  calc Real.log (1 + |chamberDeterminant X|) ≤ Real.log (2 * Real.exp (3 * chamberMass X)) :=
        Real.log_le_log (by positivity) hfinal
    _ = Real.log 2 + 3 * chamberMass X := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]

/-- **Terminal spectral transversality.**  The chamber determinant has logarithmic scale
`√X/log X`. -/
theorem chamberMass_div_three_le_log_one_add {X : ℝ} (hX : Real.exp 3 ≤ X) :
    chamberMass X / 3 ≤ Real.log (1 + |chamberDeterminant X|) := by
  have h := exp_chamberMass_div_three_sub_one_le hX
  have hpos : (0 : ℝ) < 1 + |chamberDeterminant X| := by
    have := abs_nonneg (chamberDeterminant X)
    linarith
  have hle : Real.exp (chamberMass X / 3) ≤ 1 + |chamberDeterminant X| := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (chamberMass X / 3)) hle
  rwa [Real.log_exp] at hlog

end

end RHTower
