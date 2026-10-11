import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMoment
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensityLong

/-!
# The off-line first moment beyond the critical scale decays exponentially

Write `L = log U`. For all large `U` there is one Littlewood window `[T₁, T₂]` on which, for every
`c ≥ 2`,

  `Σ_{Re ρ − ½ ≥ c/L} m_ρ (Re ρ − ½) ≤ B e^{−c/28} (T₂ − T₁) + K L²`
  (`exists_offLineTailMoment_window_le_exp`).

This improves the rate `D/c` of `exists_offLineTailMoment_window_le` to `e^{−c/28}`.

**Proof.** Every zero with `Re ρ − ½ ≥ c/L` lies in a dyadic shell `2^j c/L ≤ Re ρ − ½ < 2^{j+1} c/L`
(`exists_dyadic_level`), so its offset is at most twice the shell threshold. The zeros beyond the
`j`-th threshold are counted by the exponential near-line density
(`exists_selberg_exponential_nearLine_zeroDensity_long`) at `a = 2^{j−1} c`:
`2π (a/L) · #zeros ≤ (T₂ − T₁) A e^{−a/14} + K L`. Since `2^j ≥ j + 1`, the shell rates are at most
`r^{j+1}` with `r = e^{−c/28} ≤ e^{−1/14}`, and `Σ_j r^{j+1} ≤ r/(1 − e^{−1/14}) ≤ 15 r`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- `Σ_{j<n} r^{j+1} ≤ 15 r` for `0 ≤ r ≤ e^{−1/14}`. -/
theorem sum_range_pow_succ_le_fifteen {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ Real.exp (-(1 / 14)))
    (n : ℕ) : ∑ j ∈ Finset.range n, r ^ (j + 1) ≤ 15 * r := by
  have he : Real.exp (-(1 / 14 : ℝ)) ≤ 14 / 15 := by
    have h := Real.add_one_le_exp (1 / 14 : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hr1 : r ≤ 14 / 15 := hr.trans he
  have hgeo := geom_sum_mul_neg r n
  have hpow : 0 ≤ r ^ n := pow_nonneg hr0 n
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, r ^ i := Finset.sum_nonneg fun i _ => pow_nonneg hr0 i
  have hle : ∑ i ∈ Finset.range n, r ^ i ≤ 15 := by nlinarith
  have e : ∑ j ∈ Finset.range n, r ^ (j + 1) = r * ∑ i ∈ Finset.range n, r ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  nlinarith

/-- **The exponential off-line first moment beyond the critical scale.** For all large `U` there
is one Littlewood window on which, for every `c ≥ 2`, the zeros with `Re ρ − ½ ≥ c/log U` carry
off-line first moment at most `B e^{−c/28}(T₂ − T₁) + K log² U`. -/
theorem exists_offLineTailMoment_window_le_exp :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∀ c : ℝ, 2 ≤ c →
          ∑ w ∈ Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ≤
            B * Real.exp (-(c / 28)) * (T₂ - T₁) + K * Real.log U ^ 2 := by
  classical
  obtain ⟨A, K, hA, hK, hdens⟩ := exists_selberg_exponential_nearLine_zeroDensity_long
  refine ⟨30 * A / Real.pi, 2 * K, by positivity, by positivity, ?_⟩
  filter_upwards [hdens, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop (8 : ℝ)]
    with U hU hU4 hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ c hc2 => ?_⟩
  set L := Real.log U with hLdef
  have hL4 : 4 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hU4
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hlen0 : 0 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  set m : ℂ → ℝ := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ) with hmdef
  have hm0 : ∀ w, 0 ≤ m w := fun w => Nat.cast_nonneg _
  set Zc := Z.filter (fun w => 1 / 2 + c / L ≤ w.re)
  set J := ⌊L⌋₊ + 1
  set r : ℝ := Real.exp (-(c / 28)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  -- every zero of `Z` has real part `< 1`
  have hre1 : ∀ w ∈ Z, w.re < 1 := by
    intro w hw
    obtain ⟨-, hw0⟩ := (hZ w).mp hw
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hw0
  -- the shell sums
  set S : ℕ → ℝ := fun j => ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re), m w
    with hSdef
  have hshell : ∀ j ∈ Finset.range J, 2 ^ j * c / L * S j ≤
      ((T₂ - T₁) * (A * r ^ (j + 1)) + K * L) / Real.pi := by
    intro j _
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    set a := 2 ^ j * c / 2 with hadef
    have ha1 : 1 ≤ a := by rw [hadef]; nlinarith
    have hexp : Real.exp (-(a / 14)) ≤ r ^ (j + 1) := by
      rw [hrdef, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hj : (j : ℝ) + 1 ≤ 2 ^ j := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) j
        norm_num at this
        linarith
      push_cast
      rw [hadef]
      nlinarith
    have hrhs0 : 0 ≤ ((T₂ - T₁) * (A * r ^ (j + 1)) + K * L) / Real.pi := by positivity
    by_cases hbig : 2 * a + 2 ≤ L
    · have h := hc a ha1 hbig Z hZ
      have hfilt : Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) =
          Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re) := by
        refine Finset.filter_congr fun w _ => ?_
        have : 2 * a / L = 2 ^ j * c / L := by rw [hadef]; ring
        rw [this]
      rw [hfilt] at h
      have e : 2 ^ j * c / L * S j = (2 * Real.pi * (a / L * S j)) / Real.pi := by
        rw [hadef]; field_simp
      rw [e]
      refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hA.le) hlen0
      linarith
    · have hempty : S j = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
        exfalso
        have h1 := hre1 w hwZ
        have h2 : 1 / 2 ≤ 2 ^ j * c / L := by
          rw [le_div_iff₀ hL0]
          rw [not_le] at hbig
          rw [hadef] at hbig
          linarith
        linarith
      rw [hempty, mul_zero]
      exact hrhs0
  -- each zero of `Zc` lies in its dyadic shell
  have hlevel : ∀ w ∈ Zc, w.re - 1 / 2 ≤
      2 * ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2),
        2 ^ j * c / L := by
    intro w hw
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    obtain ⟨j, hj1, hj2⟩ := exists_dyadic_level (u := w.re - 1 / 2) hc0 hL0 (by linarith)
    have hjJ : j ∈ Finset.range J := by
      rw [Finset.mem_range]
      have h1 := hre1 w hwZ
      have hj : (2 : ℝ) ^ j * c < L := by
        rw [div_le_iff₀ hL0] at hj1
        nlinarith
      have hjl : (j : ℝ) < 2 ^ j := by
        have := Nat.lt_two_pow_self (n := j)
        exact_mod_cast this
      have hjL : (j : ℝ) < L := by nlinarith
      have : j ≤ ⌊L⌋₊ := Nat.le_floor hjL.le
      omega
    have hmem : j ∈ (Finset.range J).filter (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2) :=
      Finset.mem_filter.mpr ⟨hjJ, hj1⟩
    have hsingle := Finset.single_le_sum (f := fun j : ℕ => 2 ^ j * c / L)
      (fun i _ => by positivity) hmem
    linarith
  -- swap the sums
  have hswap : ∑ w ∈ Zc, m w * (w.re - 1 / 2) ≤
      2 * ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j := by
    calc ∑ w ∈ Zc, m w * (w.re - 1 / 2)
        ≤ ∑ w ∈ Zc, m w * (2 * ∑ j ∈ (Finset.range J).filter
            (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2), 2 ^ j * c / L) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hlevel w hw) (hm0 w)
      _ = 2 * ∑ j ∈ Finset.range J, ∑ w ∈ Zc.filter (fun w => 2 ^ j * c / L ≤ w.re - 1 / 2),
            m w * (2 ^ j * c / L) := by
          have hcomm : ∑ w ∈ Zc, m w * ∑ j ∈ (Finset.range J).filter
              (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2), 2 ^ j * c / L =
              ∑ j ∈ Finset.range J, ∑ w ∈ Zc.filter (fun w => 2 ^ j * c / L ≤ w.re - 1 / 2),
                m w * (2 ^ j * c / L) := by
            simp_rw [Finset.mul_sum, Finset.sum_filter]
            exact Finset.sum_comm
          rw [← hcomm, Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ 2 * ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by norm_num)
          rw [hSdef]
          simp only
          rw [Finset.mul_sum]
          calc ∑ w ∈ Zc.filter (fun w => 2 ^ j * c / L ≤ w.re - 1 / 2), m w * (2 ^ j * c / L)
              ≤ ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re), m w * (2 ^ j * c / L) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ =>
                  mul_nonneg (hm0 w) (by positivity)
                intro w hw
                obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
                exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw1).1, by linarith⟩
            _ = ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re), 2 ^ j * c / L * m w := by
                refine Finset.sum_congr rfl fun w _ => by ring
  -- sum the shells
  have hr14 : r ≤ Real.exp (-(1 / 14)) := Real.exp_le_exp.mpr (by linarith)
  have hgeo := sum_range_pow_succ_le_fifteen hr0 hr14 J
  have hJ : (J : ℝ) ≤ L + 1 := by
    have := Nat.floor_le hL0.le
    push_cast [J]
    linarith
  have htot : ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j ≤
      ((T₂ - T₁) * (A * (15 * r)) + (L + 1) * (K * L)) / Real.pi := by
    calc ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j
        ≤ ∑ j ∈ Finset.range J, ((T₂ - T₁) * (A * r ^ (j + 1)) + K * L) / Real.pi :=
          Finset.sum_le_sum hshell
      _ = ((T₂ - T₁) * (A * ∑ j ∈ Finset.range J, r ^ (j + 1)) + J * (K * L)) / Real.pi := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((T₂ - T₁) * (A * (15 * r)) + (L + 1) * (K * L)) / Real.pi := by
          refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
          have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo hA.le) hlen0
          have h2 := mul_le_mul_of_nonneg_right hJ (show 0 ≤ K * L by positivity)
          linarith
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hfin : 2 * (((T₂ - T₁) * (A * (15 * r)) + (L + 1) * (K * L)) / Real.pi) ≤
      30 * A / Real.pi * r * (T₂ - T₁) + 2 * K * L ^ 2 := by
    have e : 2 * (((T₂ - T₁) * (A * (15 * r)) + (L + 1) * (K * L)) / Real.pi) =
        30 * A / Real.pi * r * (T₂ - T₁) + 2 * ((L + 1) * (K * L)) / Real.pi := by
      field_simp
      ring
    rw [e]
    have h1 : 2 * ((L + 1) * (K * L)) / Real.pi ≤ 2 * K * L ^ 2 := by
      rw [div_le_iff₀ Real.pi_pos]
      have h := mul_le_mul_of_nonneg_right (show L + 1 ≤ Real.pi * L by nlinarith)
        (show 0 ≤ 2 * (K * L) by positivity)
      linarith
    linarith
  calc ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)
      = ∑ w ∈ Zc, m w * (w.re - 1 / 2) := rfl
    _ ≤ 2 * ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j := hswap
    _ ≤ 2 * (((T₂ - T₁) * (A * (15 * r)) + (L + 1) * (K * L)) / Real.pi) :=
        mul_le_mul_of_nonneg_left htot (by norm_num)
    _ ≤ 30 * A / Real.pi * r * (T₂ - T₁) + 2 * K * L ^ 2 := hfin

end

end RHTower
