import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensity
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalZeroSum

/-!
# Weighted counts of zeros right of the critical line

From the exponential near-line density (MUST-571): for all large `U` there are heights
`T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` such that for every `2/L ≤ v ≤ 1 − 2/L`, `L = log U`,
the zeros in `[½, 15/2] × [T₁, T₂]` with `Re w ≥ ½ + v` have total multiplicity
`≤ ((U/4) A e^{−vL/2400} + K L)/(πv)` (`exists_windowZeros_count_le`).

Summing over dyadic shells `v_j = 2^j v₀`, for `0 ≤ λ` with `2λ ≤ 1/4800` and `2/L ≤ v₀ ≤ 1/4`,

`Σ_{Re w > ½ + v₀} m_w e^{λ(Re w − ½)L} ≤ (U A/(4π v₀)) (1 + 4800/(v₀L)) e^{−v₀L/4800} + L · (K L/(π v₀)) e^{λL}`
(`exists_windowZeros_weighted_le`): the density decay `e^{−vL/2400}` beats the weight `e^{2λvL}`
on every shell, and the shells form a geometric series.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

open Sieve

/-- Zeros of the residue unit in the window `[½, 15/2] × [T₁, T₂]`. -/
def windowZeros (T₁ T₂ : ℝ) : Finset ℂ :=
  zetaResidueUnitClosedRectangleZeros (((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)
    (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)

theorem zetaResidueUnit_eq_zero_iff {z : ℂ} (hz : z ≠ 1) :
    zetaResidueUnit z = 0 ↔ riemannZeta z = 0 := by
  constructor
  · intro h
    by_contra hne
    exact (zetaResidueUnit_ne_zero_iff hz).2 hne h
  · intro h
    by_contra hne
    exact ((zetaResidueUnit_ne_zero_iff hz).1 hne) h

theorem mem_windowZeros_iff {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (z : ℂ) :
    z ∈ windowZeros T₁ T₂ ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
  unfold windowZeros
  rw [mem_zetaResidueUnitClosedRectangleZeros]
  have e1 : ((((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)).re = 1 / 2 := by simp
  have e2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
  have e3 : ((((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)).im = T₁ := by simp
  have e4 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
  rw [e1, e2, e3, e4]
  constructor
  · rintro ⟨hmem, hG⟩
    refine ⟨hmem, ?_⟩
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hmem
      have := (Complex.mem_reProdIm.mp hmem).2
      rw [uIcc_of_le hT] at this
      simp at this
      linarith [this.1]
    exact (zetaResidueUnit_eq_zero_iff hz1).1 hG
  · rintro ⟨hmem, hζ⟩
    refine ⟨hmem, ?_⟩
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hmem
      have := (Complex.mem_reProdIm.mp hmem).2
      rw [uIcc_of_le hT] at this
      simp at this
      linarith [this.1]
    exact (zetaResidueUnit_eq_zero_iff hz1).2 hζ

theorem zeroMult_eq_zeta_order {z : ℂ} (hz : z ≠ 1) :
    zeroMult z = ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  unfold zeroMult
  have hlinear : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz
  have h : analyticOrderAt zetaResidueUnit z = analyticOrderAt riemannZeta z := by
    calc analyticOrderAt zetaResidueUnit z =
          analyticOrderAt (fun w : ℂ => (w - 1) * riemannZeta w) z :=
        analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hz)
      _ = analyticOrderAt riemannZeta z := by
        change analyticOrderAt ((fun w : ℂ => w - 1) * riemannZeta) z = _
        rw [analyticOrderAt_mul hlinear hzeta,
          hlinear.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]
  rw [h]

/-- **The window count.** -/
theorem exists_windowZeros_count_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ v : ℝ, 2 / Real.log U ≤ v → v ≤ 1 - 2 / Real.log U →
          ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re), zeroMult w ≤
            ((U / 4) * A * Real.exp (-(v * Real.log U / 2400)) + K * Real.log U) /
              (Real.pi * v) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_exponential_nearLine_zeroDensity
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop 8] with U hU hUe hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun v hv1 hv2 => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos 4) hUe
  have hL : 4 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 4) hUe; rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log U := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv1
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  set a : ℝ := v * Real.log U / 2 with ha
  have ha1 : 1 ≤ a := by
    rw [ha, le_div_iff₀ (by norm_num)]
    have := (div_le_iff₀ hL0).mp hv1
    linarith
  have ha2 : 2 * a + 2 ≤ Real.log U := by
    rw [ha]
    have := (le_sub_iff_add_le.mp hv2)
    have h2 : 2 / Real.log U * Real.log U = 2 := by field_simp
    nlinarith
  have hZ := hcount a ha1 ha2 (windowZeros T₁ T₂) (mem_windowZeros_iff hT₁pos hT12)
  have hfilt : (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re) =
      (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 2 * a / Real.log U = v by rw [ha]; field_simp]
  rw [hfilt] at hZ
  have hsum : ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re), zeroMult w =
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have hwmem := (mem_windowZeros_iff hT₁pos hT12 w).1 (Finset.mem_filter.mp hw).1
    have hz1 : w ≠ 1 := by
      intro h
      have := (Complex.mem_reProdIm.mp hwmem.1).2
      rw [h, uIcc_of_le hT12] at this
      simp at this
      linarith [this.1]
    exact zeroMult_eq_zeta_order hz1
  rw [hsum]
  have hav : a / Real.log U = v / 2 := by rw [ha]; field_simp
  rw [hav] at hZ
  have hwidth : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
  have hS0 : 0 ≤ ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ) := Finset.sum_nonneg fun w _ => Nat.cast_nonneg _
  rw [le_div_iff₀ (by positivity)]
  have hexp : Real.exp (-(a / 1200)) = Real.exp (-(v * Real.log U / 2400)) := by
    rw [ha]; ring_nf
  rw [hexp] at hZ
  have hE : 0 ≤ A * Real.exp (-(v * Real.log U / 2400)) := by positivity
  have hmono : (T₂ - T₁) * (A * Real.exp (-(v * Real.log U / 2400))) ≤
      U / 4 * (A * Real.exp (-(v * Real.log U / 2400))) :=
    mul_le_mul_of_nonneg_right hwidth hE
  nlinarith

/-! ## Dyadic shells -/

/-- **Dyadic shell decomposition** of a monotone weight. -/
theorem sum_mult_weight_le_shells (S : Finset ℂ) {f : ℝ → ℝ} (hf0 : ∀ u, 0 ≤ f u)
    (hfm : Monotone f) {v₀ : ℝ} (hv₀ : 0 < v₀) (J : ℕ)
    (hJ : ∀ w ∈ S, w.re - 1 / 2 ≤ 2 ^ J * v₀) :
    ∑ w ∈ S.filter (fun w => 1 / 2 + v₀ < w.re), zeroMult w * f (w.re - 1 / 2) ≤
      ∑ j ∈ Finset.range J, f (2 ^ (j + 1) * v₀) *
        ∑ w ∈ S.filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re), zeroMult w := by
  classical
  have hrhs : ∑ j ∈ Finset.range J, f (2 ^ (j + 1) * v₀) *
      ∑ w ∈ S.filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re), zeroMult w =
      ∑ w ∈ S, zeroMult w * ∑ j ∈ Finset.range J,
        (if 1 / 2 + 2 ^ j * v₀ ≤ w.re then f (2 ^ (j + 1) * v₀) else 0) := by
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hrhs, Finset.sum_filter]
  refine Finset.sum_le_sum fun w hw => ?_
  split_ifs with hwv
  · have hb : v₀ < w.re - 1 / 2 := by linarith
    have hex : ∃ j : ℕ, w.re - 1 / 2 ≤ 2 ^ (j + 1) * v₀ := by
      refine ⟨J, (hJ w hw).trans ?_⟩
      have : (2 : ℝ) ^ J ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    set j₀ := Nat.find hex with hj₀
    have hj₀spec : w.re - 1 / 2 ≤ 2 ^ (j₀ + 1) * v₀ := Nat.find_spec hex
    have hj₀low : 2 ^ j₀ * v₀ < w.re - 1 / 2 := by
      rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
      · rw [h0]; simpa using hb
      · have hmin := Nat.find_min hex (show j₀ - 1 < j₀ by omega)
        rw [show j₀ - 1 + 1 = j₀ by omega] at hmin
        push Not at hmin
        exact hmin
    have hj₀J : j₀ < J := by
      by_contra hge
      push Not at hge
      have h1 : (2 : ℝ) ^ J ≤ 2 ^ j₀ := pow_le_pow_right₀ (by norm_num) hge
      have := hJ w hw
      nlinarith
    have hterm : f (w.re - 1 / 2) ≤ ∑ j ∈ Finset.range J,
        (if 1 / 2 + 2 ^ j * v₀ ≤ w.re then f (2 ^ (j + 1) * v₀) else 0) := by
      have hsingle := Finset.single_le_sum (f := fun j =>
        if 1 / 2 + 2 ^ j * v₀ ≤ w.re then f (2 ^ (j + 1) * v₀) else 0)
        (fun j _ => by split_ifs; exacts [hf0 _, le_rfl]) (Finset.mem_range.mpr hj₀J)
      rw [if_pos (by linarith)] at hsingle
      exact (hfm hj₀spec).trans hsingle
    exact mul_le_mul_of_nonneg_left hterm (zeroMult_nonneg w)
  · have : 0 ≤ ∑ j ∈ Finset.range J,
        (if 1 / 2 + 2 ^ j * v₀ ≤ w.re then f (2 ^ (j + 1) * v₀) else 0) :=
      Finset.sum_nonneg fun j _ => by split_ifs; exacts [hf0 _, le_rfl]
    exact mul_nonneg (zeroMult_nonneg w) this

/-- `Σ_{j<J} e^{−2^j c} ≤ (1 + 1/c) e^{−c}`. -/
theorem sum_exp_neg_two_pow_le {c : ℝ} (hc : 0 < c) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(2 ^ j * c)) ≤ (1 + 1 / c) * Real.exp (-c) := by
  set r : ℝ := Real.exp (-c) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ j : ℕ, Real.exp (-(2 ^ j * c)) ≤ r * r ^ j := by
    intro j
    have hj : ((j : ℝ) + 1) ≤ 2 ^ j := by
      have := Nat.lt_two_pow_self (n := j)
      exact_mod_cast (Nat.succ_le_of_lt this)
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hgeo : ∑ j ∈ Finset.range J, r ^ j ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun j _ => pow_nonneg hr0 j)
  calc ∑ j ∈ Finset.range J, Real.exp (-(2 ^ j * c))
      ≤ ∑ j ∈ Finset.range J, r * r ^ j := Finset.sum_le_sum fun j _ => hterm j
    _ = r * ∑ j ∈ Finset.range J, r ^ j := by rw [Finset.mul_sum]
    _ ≤ r * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeo hr0
    _ ≤ (1 + 1 / c) * r := by
        have h1r : 0 < 1 - r := by linarith
        rw [← div_eq_mul_inv, div_le_iff₀ h1r]
        -- `r ≤ (1 + 1/c) r (1 − r)` ⟸ `1 ≤ (1 + 1/c)(1 − e^{−c})` ⟸ `e^c ≥ 1 + c`
        have hec : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
        have hrexp : r * Real.exp c = 1 := by rw [hr, ← Real.exp_add]; simp
        have key : 1 ≤ (1 + 1 / c) * (1 - r) := by
          have h1 : r ≤ 1 / (1 + c) := by
            rw [le_div_iff₀ (by linarith)]
            nlinarith
          have : (1 + 1 / c) * (1 - 1 / (1 + c)) = 1 := by field_simp; ring
          nlinarith [show 0 < 1 + 1 / c by positivity]
        nlinarith

/-- One dyadic shell: `e^{2^{j+1}λ v₀ L} · N_j ≤ (UA/(4πv₀)) e^{−2^j v₀ L/4800} + (KL/(πv₀)) e^{λL}`
when `N_j ≤ ((U/4)A e^{−2^j v₀ L/2400} + KL)/(π 2^j v₀)`. -/
theorem shell_term_le {U A K L lam v₀ N : ℝ} (j : ℕ) (hU : 0 ≤ U) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hlam : 0 ≤ lam) (hlam2 : 2 * lam ≤ 1 / 4800) (hv₀ : 0 < v₀)
    (hj : 2 ^ (j + 1) * v₀ ≤ 1)
    (hN : N ≤ ((U / 4) * A * Real.exp (-(2 ^ j * v₀ * L / 2400)) + K * L) /
      (Real.pi * (2 ^ j * v₀))) :
    Real.exp (lam * (2 ^ (j + 1) * v₀) * L) * N ≤
      U * A / (4 * Real.pi * v₀) * Real.exp (-(2 ^ j * v₀ * L / 4800)) +
        K * L / (Real.pi * v₀) * Real.exp (lam * L) := by
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hc0 : 0 < 2 ^ j * v₀ := by positivity
  have hE1 : Real.exp (lam * (2 ^ (j + 1) * v₀) * L) * Real.exp (-(2 ^ j * v₀ * L / 2400)) ≤
      Real.exp (-(2 ^ j * v₀ * L / 4800)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hpow]
    have : 0 ≤ 2 ^ j * v₀ * L := by positivity
    nlinarith
  have hE2 : Real.exp (lam * (2 ^ (j + 1) * v₀) * L) ≤ Real.exp (lam * L) := by
    apply Real.exp_le_exp.mpr
    have : lam * (2 ^ (j + 1) * v₀) ≤ lam := mul_le_of_le_one_right hlam hj
    nlinarith
  have hinv : 1 / (Real.pi * (2 ^ j * v₀)) ≤ 1 / (Real.pi * v₀) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le
  set e := Real.exp (lam * (2 ^ (j + 1) * v₀) * L) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  calc e * N ≤ e * (((U / 4) * A * Real.exp (-(2 ^ j * v₀ * L / 2400)) + K * L) /
        (Real.pi * (2 ^ j * v₀))) := mul_le_mul_of_nonneg_left hN he0
    _ = ((U / 4) * A * (e * Real.exp (-(2 ^ j * v₀ * L / 2400))) + K * L * e) *
        (1 / (Real.pi * (2 ^ j * v₀))) := by ring
    _ ≤ ((U / 4) * A * Real.exp (-(2 ^ j * v₀ * L / 4800)) + K * L * Real.exp (lam * L)) *
        (1 / (Real.pi * v₀)) := by
        apply mul_le_mul _ hinv (by positivity) (by positivity)
        have h1 := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ (U / 4) * A by positivity)
        have h2 := mul_le_mul_of_nonneg_left hE2 (show 0 ≤ K * L by positivity)
        linarith
    _ = _ := by field_simp

theorem windowZeros_re_lt_one {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) {w : ℂ}
    (hw : w ∈ windowZeros T₁ T₂) : w.re < 1 := by
  have h := ((mem_windowZeros_iff hT₁ hT w).1 hw).2
  by_contra hge
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) h

/-- **Weighted window count.** For `0 ≤ λ` with `2λ ≤ 1/4800` and `2/L ≤ v₀ ≤ 1/4`,
`Σ_{Re w > ½ + v₀} m_w e^{λ(Re w − ½)L} ≤ (UA/(4πv₀))(1 + 4800/(v₀L)) e^{−v₀L/4800} + L (KL/(πv₀)) e^{λL}`. -/
theorem exists_windowZeros_weighted_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ lam v₀ : ℝ, 0 ≤ lam → 2 * lam ≤ 1 / 4800 → 2 / Real.log U ≤ v₀ → v₀ ≤ 1 / 4 →
          ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
              zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log U) ≤
            U * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
                Real.exp (-(v₀ * Real.log U / 4800)) +
              Real.log U * (K * Real.log U / (Real.pi * v₀) * Real.exp (lam * Real.log U)) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_windowZeros_count_le
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop 8] with U hU hUe hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun lam v₀ hlam hlam2 hv1 hv2 => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos 4) hUe
  set L := Real.log U with hLdef
  have hL : 4 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 4) hUe; rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < v₀ := lt_of_lt_of_le (by positivity) hv1
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  set J : ℕ := ⌊L⌋₊ with hJ
  have hJL : (J : ℝ) ≤ L := Nat.floor_le hL0.le
  have hJpow : L < 2 ^ J := by
    have h1 := Nat.lt_floor_add_one L
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt Nat.lt_two_pow_self
    push_cast at h2
    rw [← hJ] at h1
    linarith
  have hcover : ∀ w ∈ windowZeros T₁ T₂, w.re - 1 / 2 ≤ 2 ^ J * v₀ := by
    intro w hw
    have h1 := windowZeros_re_lt_one hT₁pos hT12 hw
    have h2 : 2 ≤ 2 ^ J * v₀ := by
      have := (div_le_iff₀ hL0).mp hv1
      nlinarith
    linarith
  have hfm : Monotone (fun b : ℝ => Real.exp (lam * b * L)) := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hab hlam
    nlinarith
  have hsh := sum_mult_weight_le_shells (windowZeros T₁ T₂) (f := fun b => Real.exp (lam * b * L))
    (fun _ => (Real.exp_pos _).le) hfm hv0 J hcover
  refine hsh.trans ?_
  set c : ℝ := v₀ * L / 4800 with hc
  have hc0 : 0 < c := by positivity
  have hterm : ∀ j ∈ Finset.range J, Real.exp (lam * (2 ^ (j + 1) * v₀) * L) *
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re), zeroMult w ≤
      U * A / (4 * Real.pi * v₀) * Real.exp (-(2 ^ j * c)) +
        K * L / (Real.pi * v₀) * Real.exp (lam * L) := by
    intro j _
    have hrhs0 : 0 ≤ U * A / (4 * Real.pi * v₀) * Real.exp (-(2 ^ j * c)) +
        K * L / (Real.pi * v₀) * Real.exp (lam * L) := by positivity
    have hexpc : -(2 ^ j * c) = -(2 ^ j * v₀ * L / 4800) := by rw [hc]; ring
    by_cases hjv : 2 ^ j * v₀ ≤ 1 / 2
    · have hj1 : 2 ^ (j + 1) * v₀ ≤ 1 := by rw [pow_succ]; linarith
      have hvle : 2 ^ j * v₀ ≤ 1 - 2 / L := by
        have : 2 / L ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
        linarith
      have hvge : 2 / L ≤ 2 ^ j * v₀ := by
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      have hN := hcount (2 ^ j * v₀) hvge hvle
      rw [hexpc]
      exact shell_term_le j hU0.le hA.le hK hL0.le hlam hlam2 hv0 hj1 hN
    · push Not at hjv
      have hempty : (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun w hw hle => ?_
        have := windowZeros_re_lt_one hT₁pos hT12 hw
        linarith
      rw [hempty, Finset.sum_empty, mul_zero]
      exact hrhs0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeo := sum_exp_neg_two_pow_le hc0 J
  have h1c : 1 + 1 / c = 1 + 4800 / (v₀ * L) := by rw [hc]; field_simp
  rw [h1c] at hgeo
  have hpos : 0 ≤ U * A / (4 * Real.pi * v₀) := by positivity
  have hsecond : 0 ≤ K * L / (Real.pi * v₀) * Real.exp (lam * L) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hgeo hpos
  have h2 := mul_le_mul_of_nonneg_right hJL hsecond
  rw [hc] at h1
  nlinarith

end RHTower
