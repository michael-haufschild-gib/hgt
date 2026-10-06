import GaloisForLFunctions.RHTower.SelbergNearLineCriticalGateDensity
import GaloisForLFunctions.RHTower.Sieve.InghamNearHalfZeroCount
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount

/-!
# The Gaussian-weighted off-line zero sum is `o(T log² T)`

For the zeros `ρ = β + iγ` of `ζ` right of the critical line,

`Σ_{β > 1/2, 1 ≤ γ ≤ Y} γ^{β − 1/2} e^{−γ²/T²} ≤ ε T (log T)²`

for every `ε > 0`, all large `T` and every `Y ≥ 1` (`eventually_offLineWeight_le`), zeros counted with
multiplicity. This is the density input of the finite-type uniqueness theorem: the off-line zeros
carry the weight `(γ/2π)^{|β−1/2|}` there, and the main terms are of order `T log² T`.

On one height block `[S, 2S]`, with `λ = log 2S`, the weight `(2S)^{β−1/2}` is at most
`e Σ_{j < λ(β−1/2)} e^j`, so the block sum is `≤ e Σ_j e^j N_j`, `N_j` the number of zeros with
`β > 1/2 + j/λ`. Three counts bound `N_j`:

* `j ≤ 1`: all zeros of the block, `O(S log S)`;
* `2 ≤ j ≤ 6 log λ`: the near-line density at rate `22/25`
  (`exists_selberg_criticalGate_nearLine_zeroDensity`) together with the local count at the two ends
  of the block, giving `N_j ≪ (λ/j)(S e^{−0.845 j} + λ) + log S`;
* `j ≥ 6 log λ`: the Ingham–Gabriel density at rate `6/5`
  (`exists_eventually_zeroCountAbove_le_nearHalf`), `N_j ≪ (λ/j) S e^{−6j/5} λ²`.

Hence the block sum is `O(S λ^{39/20})` (`exists_eventually_offLineBlock_le`), and summing the blocks
`[2^k, 2^{k+1}]` against `e^{−4^k/T²}` gives `O(T (log T)^{39/20})`.
-/

noncomputable section

open Complex Set Filter MeasureTheory Metric

namespace RHTower

/-! ## Multiplicities and the local count -/

/-- Off the pole, `(s − 1)ζ(s)` and `ζ` have the same analytic order. -/
theorem analyticOrderAt_zetaResidueUnit_eq_zeta {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt zetaResidueUnit s = analyticOrderAt riemannZeta s := by
  have hlinear : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  calc analyticOrderAt zetaResidueUnit s =
        analyticOrderAt (fun z : ℂ => (z - 1) * riemannZeta z) s :=
        analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hs)
    _ = analyticOrderAt riemannZeta s := by
        change analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) s = _
        rw [analyticOrderAt_mul hlinear hzeta,
          hlinear.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs), zero_add]

/-- A zero of the residue unit in a rectangle above height `0` is a zero of `ζ` in the strip. -/
theorem zero_data_of_mem_rectangleZeros {c d A B : ℝ} (hA : 0 < A) {w : ℂ}
    (hw : w ∈ Sieve.zetaResidueUnitClosedRectangleZeros ((c : ℂ) + (A : ℂ) * I)
      ((d : ℂ) + (B : ℂ) * I)) (hcd : c ≤ d) (hAB : A ≤ B) :
    c ≤ w.re ∧ w.re ≤ d ∧ A ≤ w.im ∧ w.im ≤ B ∧ w ≠ 1 ∧ riemannZeta w = 0 ∧ w.re < 1 := by
  have hwmem := Sieve.mem_zetaResidueUnitClosedRectangleZeros.mp hw
  have hwK := Complex.mem_reProdIm.mp hwmem.1
  have hre : w.re ∈ Set.Icc c d := by simpa [uIcc_of_le hcd] using hwK.1
  have him : w.im ∈ Set.Icc A B := by simpa [uIcc_of_le hAB] using hwK.2
  have hw1 : w ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
    linarith [him.1]
  have hzeta : riemannZeta w = 0 := by
    by_contra hne
    exact ((Sieve.zetaResidueUnit_ne_zero_iff hw1).2 hne) hwmem.2
  have hre1 : w.re < 1 := by
    by_contra hcon
    exact (riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon)) hzeta
  exact ⟨hre.1, hre.2, him.1, him.2, hw1, hzeta, hre1⟩

/-- **Local count in rectangle form.** For `t ≥ 4`, the zeros right of `1/2` with ordinate within `1`
of `t` have total multiplicity at most `20 log(180 t)`. -/
theorem sum_rectangleZeros_window_le {t c d A B : ℝ} (ht : 4 ≤ t) (hc : 1 / 2 ≤ c) (hcd : c ≤ d)
    (hAB : A ≤ B) (hA : t - 1 ≤ A) (hB : B ≤ t + 1) :
    (∑ w ∈ Sieve.zetaResidueUnitClosedRectangleZeros ((c : ℂ) + (A : ℂ) * I)
        ((d : ℂ) + (B : ℂ) * I), ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)) ≤
      20 * Real.log (180 * t) := by
  classical
  have ht' : 4 ≤ |t| := by rw [abs_of_pos (by linarith)]; exact ht
  set Z := Sieve.zetaResidueUnitClosedRectangleZeros ((c : ℂ) + (A : ℂ) * I) ((d : ℂ) + (B : ℂ) * I)
  set D := MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|) with hD
  have hdata : ∀ w ∈ Z, w ∈ closedBall ((2 : ℂ) + t * I) |1.85| ∧
      ((analyticOrderAt zetaResidueUnit w).toNat : ℤ) = D w := by
    intro w hw
    obtain ⟨hc', -, hA', hB', hw1, hzeta, hre1⟩ :=
      zero_data_of_mem_rectangleZeros (by linarith) hw hcd hAB
    have hdisc : w ∈ closedBall ((2 : ℂ) + t * I) |1.85| :=
      mem_disc_of_window (by linarith) hre1 (abs_le.mpr ⟨by linarith, by linarith⟩)
    refine ⟨hdisc, ?_⟩
    have hstrip : 0 < w.re ∧ w.re < 1 := ⟨by linarith, hre1⟩
    rw [← divisor_xi_eq_divisor_zeta_disc ht' hdisc,
      Sieve.analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip hstrip,
      MeromorphicOn.AnalyticOnNhd.divisor_apply (xi_analyticOnNhd _) (Set.mem_univ w),
      ← ENat.coe_toNat (xi_orderAt_ne_top w)]
    simp
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  set F : Finset ℂ := hfin.toFinset with hF
  have hsupp : Function.support (fun u => D u) ⊆ (F : Set ℂ) := by
    intro u hu
    rw [hF, Set.Finite.coe_toFinset]
    exact hu
  have hfinsum : (∑ᶠ u, D u) = ∑ u ∈ F, D u := finsum_eq_sum_of_support_subset _ hsupp
  have hZF : (∑ w ∈ Z, D w) ≤ ∑ u ∈ F, D u := by
    calc (∑ w ∈ Z, D w) ≤ ∑ w ∈ Z ∪ F, D w :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            (fun ρ _ _ => divisor_zeta_disc_nonneg ht' ρ)
      _ = ∑ u ∈ F, D u := by
          symm
          refine Finset.sum_subset Finset.subset_union_right fun ρ _ hρF => ?_
          by_contra hne
          exact hρF (by rw [hF, Set.Finite.mem_toFinset]; exact hne)
  have hint : (∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℤ)) ≤ ∑ᶠ u, D u := by
    rw [hfinsum]
    refine le_trans (le_of_eq ?_) hZF
    exact Finset.sum_congr rfl fun w hw => (hdata w hw).2
  have hreal : (∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)) ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) := by exact_mod_cast hint
  have h := zeta_disc_zeroCount_le ht'
  rw [abs_of_pos (by linarith : (0 : ℝ) < t)] at h
  exact hreal.trans h

/-! ## Discretising the weight -/

/-- `e^{λx} ≤ e Σ_{j ≤ J} e^j [j < λx]` for `0 < λx ≤ J + 1`. -/
theorem exp_le_e_mul_sum_indicator {y : ℝ} {J : ℕ} (hy : 0 < y) (hyJ : y ≤ J + 1) :
    Real.exp y ≤ Real.exp 1 * ∑ j ∈ Finset.range (J + 1),
      Real.exp j * (if (j : ℝ) < y then 1 else 0) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℝ) < y ∧ y ≤ k + 1 := by
    refine ⟨⌈y⌉₊ - 1, ?_, ?_⟩
    · have h1 : (1 : ℕ) ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hy).ne'
      rw [Nat.cast_sub h1, Nat.cast_one]
      linarith [Nat.ceil_lt_add_one hy.le]
    · have h1 : (1 : ℕ) ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hy).ne'
      rw [Nat.cast_sub h1, Nat.cast_one]
      linarith [Nat.le_ceil y]
  have hkJ : k ≤ J := by
    have : (k : ℝ) < J + 1 := lt_of_lt_of_le hk.1 hyJ
    exact_mod_cast (Nat.lt_succ_iff.mp (by exact_mod_cast this))
  have hterm : Real.exp k ≤ ∑ j ∈ Finset.range (J + 1),
      Real.exp j * (if (j : ℝ) < y then 1 else 0) := by
    have hmem : k ∈ Finset.range (J + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkJ)
    have h := Finset.single_le_sum (f := fun j : ℕ => Real.exp j * (if (j : ℝ) < y then 1 else 0))
      (fun j _ => by positivity) hmem
    simpa [if_pos hk.1] using h
  calc Real.exp y ≤ Real.exp (1 + k) := Real.exp_le_exp.mpr (by linarith [hk.2])
    _ = Real.exp 1 * Real.exp k := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (Real.exp_pos 1).le

/-- **Layer decomposition of a weighted zero sum.** -/
theorem sum_weight_le_layers {F : Finset ℂ} {m : ℂ → ℝ} {lam : ℝ} {J : ℕ} (hlam : 0 < lam)
    (hm : ∀ w ∈ F, 0 ≤ m w) (hF : ∀ w ∈ F, 1 / 2 < w.re ∧ lam * (w.re - 1 / 2) ≤ J + 1) :
    ∑ w ∈ F, m w * Real.exp (lam * (w.re - 1 / 2)) ≤
      Real.exp 1 * ∑ j ∈ Finset.range (J + 1), Real.exp j *
        ∑ w ∈ F.filter (fun w => 1 / 2 + j / lam < w.re), m w := by
  classical
  have hpt : ∀ w ∈ F, m w * Real.exp (lam * (w.re - 1 / 2)) ≤
      m w * (Real.exp 1 * ∑ j ∈ Finset.range (J + 1),
        Real.exp j * (if (j : ℝ) < lam * (w.re - 1 / 2) then 1 else 0)) := by
    intro w hw
    have hy : 0 < lam * (w.re - 1 / 2) := mul_pos hlam (by linarith [(hF w hw).1])
    exact mul_le_mul_of_nonneg_left (exp_le_e_mul_sum_indicator hy (hF w hw).2) (hm w hw)
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  have hiff : ∀ (j : ℕ) (w : ℂ), ((j : ℝ) < lam * (w.re - 1 / 2)) ↔ (1 / 2 + j / lam < w.re) := by
    intro j w
    rw [show (1 / 2 + (j : ℝ) / lam < w.re) ↔ ((j : ℝ) / lam < w.re - 1 / 2) from
      ⟨fun h => by linarith, fun h => by linarith⟩, div_lt_iff₀ hlam, mul_comm]
  have hrw : ∀ w : ℂ, m w * (Real.exp 1 * ∑ j ∈ Finset.range (J + 1),
      Real.exp j * (if (j : ℝ) < lam * (w.re - 1 / 2) then 1 else 0)) =
      Real.exp 1 * ∑ j ∈ Finset.range (J + 1),
        Real.exp j * (if 1 / 2 + j / lam < w.re then m w else 0) := by
    intro w
    rw [← mul_assoc, mul_comm (m w) (Real.exp 1), mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (j : ℝ) < lam * (w.re - 1 / 2)
    · rw [if_pos h, if_pos ((hiff j w).mp h)]; ring
    · rw [if_neg h, if_neg (fun h' => h ((hiff j w).mpr h'))]; ring
  rw [Finset.sum_congr rfl (fun w _ => hrw w), ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, Finset.sum_filter]

/-! ## Counts in one height block -/

/-- The zeros right of `1/2` (as residue-unit zeros) with ordinate in `[A, B]`. -/
abbrev blockZeros (A B : ℝ) : Finset ℂ :=
  Sieve.zetaResidueUnitClosedRectangleZeros (((1 / 2 : ℝ) : ℂ) + (A : ℂ) * I) ((4 : ℂ) + (B : ℂ) * I)

/-- The multiplicity `(analyticOrderAt ((s−1)ζ(s)) w).toNat` as a real number. -/
abbrev zeroMult (w : ℂ) : ℝ := ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)

theorem zeroMult_nonneg (w : ℂ) : 0 ≤ zeroMult w := Nat.cast_nonneg _

theorem mem_blockZeros_iff {A B : ℝ} (hAB : A ≤ B) {w : ℂ} :
    w ∈ blockZeros A B ↔ (1 / 2 ≤ w.re ∧ w.re ≤ 4) ∧ (A ≤ w.im ∧ w.im ≤ B) ∧
      zetaResidueUnit w = 0 := by
  rw [blockZeros, Sieve.mem_zetaResidueUnitClosedRectangleZeros, Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add,
    Complex.re_ofNat, Complex.im_ofNat, add_zero]
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 4), uIcc_of_le hAB]
  simp only [Set.mem_Icc]
  tauto

/-- All zeros of a block: `O(S log S)`. -/
theorem exists_sum_blockZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : ℝ}, 1 ≤ S →
      (∑ w ∈ blockZeros S (2 * S), zeroMult w) ≤ C * (2 * S + 4) * Real.log (2 * S + 5) := by
  obtain ⟨C, hC, hglob⟩ := Sieve.exists_zetaResidueUnitClosedRectangleMultiplicity_le_global
  refine ⟨C, hC, fun {S} hS => ?_⟩
  refine le_trans ?_ (hglob (c := 1 / 2) (T := 2 * S) (by norm_num) (by norm_num) (by linarith))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w _ _ => zeroMult_nonneg w)
  intro w hw
  rw [mem_blockZeros_iff (by linarith)] at hw
  rw [Sieve.mem_zetaResidueUnitClosedRectangleZeros, Complex.mem_reProdIm]
  have hre1 : ((((1 / 2 : ℝ) : ℂ) + ((-(2 * S) : ℝ) : ℂ) * I)).re = 1 / 2 := by simp
  have hre2 : ((4 : ℂ) + ((2 * S : ℝ) : ℂ) * I).re = 4 := by simp
  have him1 : ((((1 / 2 : ℝ) : ℂ) + ((-(2 * S) : ℝ) : ℂ) * I)).im = -(2 * S) := by simp
  have him2 : ((4 : ℂ) + ((2 * S : ℝ) : ℂ) * I).im = 2 * S := by simp
  refine ⟨⟨?_, ?_⟩, hw.2.2⟩
  · rw [hre1, hre2, uIcc_of_le (by norm_num)]
    exact ⟨hw.1.1, hw.1.2⟩
  · rw [him1, him2, uIcc_of_le (by linarith)]
    exact ⟨by linarith [hw.2.1.1], hw.2.1.2⟩

theorem sum_union_le_of_nonneg {s t : Finset ℂ} {f : ℂ → ℝ} (hf : ∀ w, 0 ≤ f w) :
    ∑ w ∈ s ∪ t, f w ≤ (∑ w ∈ s, f w) + ∑ w ∈ t, f w := by
  classical
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ w ∈ s ∩ t, f w := Finset.sum_nonneg fun w _ => hf w
  linarith

/-- The block sum splits along `A ≤ T₁ ≤ T₂ ≤ B`. -/
theorem sum_blockZeros_filter_le_split {A B T₁ T₂ σ : ℝ} (hAT : A ≤ T₁) (hT : T₁ ≤ T₂)
    (hTB : T₂ ≤ B) :
    (∑ w ∈ (blockZeros A B).filter (fun w => σ < w.re), zeroMult w) ≤
      (∑ w ∈ blockZeros A T₁, zeroMult w) +
        (∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w) +
        ∑ w ∈ blockZeros T₂ B, zeroMult w := by
  classical
  have hsub : (blockZeros A B).filter (fun w => σ < w.re) ⊆
      blockZeros A T₁ ∪ ((blockZeros T₁ T₂).filter (fun w => σ < w.re) ∪ blockZeros T₂ B) := by
    intro w hw
    rw [Finset.mem_filter, mem_blockZeros_iff (by linarith)] at hw
    rcases le_or_gt w.im T₁ with h1 | h1
    · exact Finset.mem_union_left _ ((mem_blockZeros_iff hAT).mpr ⟨hw.1.1, ⟨hw.1.2.1.1, h1⟩, hw.1.2.2⟩)
    · rcases le_or_gt w.im T₂ with h2 | h2
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
        rw [Finset.mem_filter, mem_blockZeros_iff hT]
        exact ⟨⟨hw.1.1, ⟨h1.le, h2⟩, hw.1.2.2⟩, hw.2⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
        exact (mem_blockZeros_iff hTB).mpr ⟨hw.1.1, ⟨h2.le, hw.1.2.1.2⟩, hw.1.2.2⟩
  calc (∑ w ∈ (blockZeros A B).filter (fun w => σ < w.re), zeroMult w)
      ≤ ∑ w ∈ blockZeros A T₁ ∪ ((blockZeros T₁ T₂).filter (fun w => σ < w.re) ∪
          blockZeros T₂ B), zeroMult w :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => zeroMult_nonneg w)
    _ ≤ (∑ w ∈ blockZeros A T₁, zeroMult w) +
          ∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re) ∪ blockZeros T₂ B, zeroMult w :=
        sum_union_le_of_nonneg (fun w => zeroMult_nonneg w)
    _ ≤ (∑ w ∈ blockZeros A T₁, zeroMult w) +
          ((∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w) +
            ∑ w ∈ blockZeros T₂ B, zeroMult w) := by
        gcongr
        exact sum_union_le_of_nonneg (fun w => zeroMult_nonneg w)
    _ = _ := by ring

/-- **Near-line block count** from the critical-gate density on `[T₁, T₂]`. -/
theorem sum_blockZeros_filter_le_nearLine {T₁ T₂ L a A K σ : ℝ} (hT₁ : 20 ≤ T₁) (hT : T₁ ≤ T₂)
    (hL : 0 < L) (ha : 0 < a) (hσ : 1 / 2 + 51 / 50 * (a / L) ≤ σ)
    (hD3 : ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
      2 * Real.pi * ((a / L) *
        ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
        (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L) :
    (∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w) ≤
      L / (2 * Real.pi * a) * ((T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L) := by
  classical
  set Z := Sieve.zetaResidueUnitClosedRectangleZeros (((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)
    (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I) with hZ
  have hne1 : ∀ z : ℂ, T₁ ≤ z.im → z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    simp at hz
    linarith
  have hZmem : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
    intro z
    rw [hZ, Sieve.mem_zetaResidueUnitClosedRectangleZeros]
    have hre1 : ((((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)).re = 1 / 2 := by simp
    have hre2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
    have him1 : ((((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)).im = T₁ := by simp
    have him2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
    rw [hre1, hre2, him1, him2]
    constructor
    · rintro ⟨hrect, hz⟩
      have himz : T₁ ≤ z.im := by
        have := (Complex.mem_reProdIm.mp hrect).2
        rw [uIcc_of_le hT] at this
        exact this.1
      exact ⟨hrect, by
        by_contra hne
        exact (Sieve.zetaResidueUnit_ne_zero_iff (hne1 z himz)).2 hne hz⟩
    · rintro ⟨hrect, hz⟩
      have himz : T₁ ≤ z.im := by
        have := (Complex.mem_reProdIm.mp hrect).2
        rw [uIcc_of_le hT] at this
        exact this.1
      refine ⟨hrect, ?_⟩
      by_contra hne
      exact ((Sieve.zetaResidueUnit_ne_zero_iff (hne1 z himz)).1 hne) hz
  have hcount := hD3 Z hZmem
  have hsub : (blockZeros T₁ T₂).filter (fun w => σ < w.re) ⊆
      Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re) := by
    intro w hw
    rw [Finset.mem_filter, mem_blockZeros_iff hT] at hw
    rw [Finset.mem_filter, hZmem]
    refine ⟨⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩, by linarith [hw.2]⟩
    · rw [uIcc_of_le (by norm_num)]; exact ⟨hw.1.1.1, by linarith [hw.1.1.2]⟩
    · rw [uIcc_of_le hT]; exact hw.1.2.1
    · by_contra hne
      exact ((Sieve.zetaResidueUnit_ne_zero_iff (hne1 w hw.1.2.1.1)).2 hne) hw.1.2.2
  have hle : (∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w) ≤
      ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    calc (∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w)
        = ∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [Finset.mem_filter, mem_blockZeros_iff hT] at hw
          rw [zeroMult, analyticOrderAt_zetaResidueUnit_eq_zeta (hne1 w hw.1.2.1.1)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => Nat.cast_nonneg _)
  have hpos : 0 < 2 * Real.pi * a / L := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (a / L))
  have h3 : 2 * Real.pi * (a / L) * (∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
      (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L := by
    rw [mul_assoc]; exact hcount
  have h4 : (∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w) *
      (2 * Real.pi * a) = L * (2 * Real.pi * (a / L) *
        ∑ w ∈ (blockZeros T₁ T₂).filter (fun w => σ < w.re), zeroMult w) := by
    field_simp
  rw [h4]
  have := h2.trans h3
  nlinarith

/-- **Gabriel block count** from the full-strip density. -/
theorem sum_blockZeros_filter_le_gabriel {S X u : ℝ} (hS : 1 ≤ S) (hX : 2 * S ≤ X - 2)
    (hu : 0 < u) :
    (∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 + u < w.re), zeroMult w) ≤
      Sieve.zetaLittlewoodZeroCountAbove (1 / 2 + 19 / 20 * u) 4 (X - 2) (1 / 2 + u) := by
  classical
  unfold Sieve.zetaLittlewoodZeroCountAbove
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w _ _ => Nat.cast_nonneg _)
  intro w hw
  rw [Finset.mem_filter, mem_blockZeros_iff (by linarith)] at hw
  rw [Finset.mem_filter, Sieve.mem_zetaResidueUnitClosedRectangleZeros, Complex.mem_reProdIm]
  have hre1 : (((1 / 2 + 19 / 20 * u : ℝ) : ℂ) + ((-(X - 2) : ℝ) : ℂ) * I).re =
      1 / 2 + 19 / 20 * u := by simp
  have hre2 : (((4 : ℝ) : ℂ) + ((X - 2 : ℝ) : ℂ) * I).re = 4 := by simp
  have him1 : (((1 / 2 + 19 / 20 * u : ℝ) : ℂ) + ((-(X - 2) : ℝ) : ℂ) * I).im = -(X - 2) := by
    simp
  have him2 : (((4 : ℝ) : ℂ) + ((X - 2 : ℝ) : ℂ) * I).im = X - 2 := by simp
  rw [hre1, hre2, him1, him2, uIcc_of_le (by linarith [hw.1.1.2]), uIcc_of_le (by linarith)]
  exact ⟨⟨⟨⟨by linarith [hw.2], hw.1.1.2⟩, ⟨by linarith [hw.1.2.1.1], by linarith [hw.1.2.1.2]⟩⟩,
    hw.1.2.2⟩, hw.2.le⟩

/-! ## The layer sum -/

/-- **The layer sum** split at `1 < J₁`: counts bounded by `N₀` for `j ≤ 1`, by `E₁ + R e^{−κj}` for
`2 ≤ j ≤ J₁`, and by `G e^{−6j/5}` beyond. -/
theorem layer_sum_le {N : ℕ → ℝ} {J J₁ : ℕ} {N₀ E₁ R G κ : ℝ} (hκ : κ ≤ 1)
    (hN₀ : 0 ≤ N₀) (hE₁ : 0 ≤ E₁) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hB0 : ∀ j ≤ 1, N j ≤ N₀)
    (hB1 : ∀ j, 2 ≤ j → j ≤ J₁ → N j ≤ E₁ + R * Real.exp (-(κ * j)))
    (hB2 : ∀ j, J₁ < j → j ≤ J → N j ≤ G * Real.exp (-(6 / 5 * j))) :
    ∑ j ∈ Finset.range (J + 1), Real.exp j * N j ≤
      (1 + Real.exp 1) * N₀ +
        (J₁ + 1) * (Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁)) +
        G * (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ)))) := by
  classical
  set f₀ : ℕ → ℝ := fun j => if j ≤ 1 then Real.exp j * N₀ else 0
  set f₁ : ℕ → ℝ := fun j => if 2 ≤ j ∧ j ≤ J₁ then
    Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁) else 0
  set f₂ : ℕ → ℝ := fun j => if J₁ < j then G * Real.exp (-(1 / 5 : ℝ)) ^ j else 0
  have hpt : ∀ j ∈ Finset.range (J + 1), Real.exp j * N j ≤ f₀ j + f₁ j + f₂ j := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have he : 0 < Real.exp (j : ℝ) := Real.exp_pos _
    rcases le_or_gt j 1 with h1 | h1
    · have h := mul_le_mul_of_nonneg_left (hB0 j h1) he.le
      simp only [f₀, f₁, f₂, if_pos h1, if_neg (show ¬(2 ≤ j ∧ j ≤ J₁) by omega)]
      rcases le_or_gt j J₁ with h2 | h2
      · rw [if_neg (by omega)]; linarith
      · rw [if_pos h2]
        have : 0 ≤ G * Real.exp (-(1 / 5 : ℝ)) ^ j := by positivity
        linarith
    · rcases le_or_gt j J₁ with h2 | h2
      · have hb := hB1 j (by omega) h2
        simp only [f₀, f₁, f₂, if_neg (show ¬ j ≤ 1 by omega), if_pos (show 2 ≤ j ∧ j ≤ J₁ by omega),
          if_neg (show ¬ J₁ < j by omega)]
        have hjJ₁ : (j : ℝ) ≤ J₁ := by exact_mod_cast h2
        have h3 : Real.exp (j : ℝ) * N j ≤ Real.exp j * (E₁ + R * Real.exp (-(κ * j))) :=
          mul_le_mul_of_nonneg_left hb he.le
        have h4 : Real.exp (j : ℝ) * E₁ ≤ Real.exp J₁ * E₁ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hjJ₁) hE₁
        have h5 : Real.exp (j : ℝ) * (R * Real.exp (-(κ * j))) ≤ R * Real.exp ((1 - κ) * J₁) := by
          rw [mul_left_comm, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hR
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
        nlinarith
      · have hb := hB2 j h2 hjJ
        simp only [f₀, f₁, f₂, if_neg (show ¬ j ≤ 1 by omega), if_neg (show ¬(2 ≤ j ∧ j ≤ J₁) by omega),
          if_pos h2, zero_add]
        have h3 : Real.exp (j : ℝ) * N j ≤ Real.exp j * (G * Real.exp (-(6 / 5 * j))) :=
          mul_le_mul_of_nonneg_left hb he.le
        have h4 : Real.exp (j : ℝ) * (G * Real.exp (-(6 / 5 * j))) =
            G * Real.exp (-(1 / 5 : ℝ)) ^ j := by
          rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
          congr 2
          ring
        linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs0 : ∑ j ∈ Finset.range (J + 1), f₀ j ≤ (1 + Real.exp 1) * N₀ := by
    have h1 : ∑ j ∈ Finset.range (J + 1), f₀ j =
        ∑ j ∈ (Finset.range (J + 1)).filter (fun j => j ≤ 1), Real.exp j * N₀ := by
      rw [Finset.sum_filter]
    have h2 : (Finset.range (J + 1)).filter (fun j => j ≤ 1) ⊆ Finset.range 2 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact Finset.mem_range.mpr (by omega)
    rw [h1]
    calc ∑ j ∈ (Finset.range (J + 1)).filter (fun j => j ≤ 1), Real.exp j * N₀
        ≤ ∑ j ∈ Finset.range 2, Real.exp j * N₀ :=
          Finset.sum_le_sum_of_subset_of_nonneg h2 (fun j _ _ => by positivity)
      _ = (1 + Real.exp 1) * N₀ := by
          simp [Finset.sum_range_succ]
          ring
  have hc0 : 0 ≤ Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁) := by positivity
  have hs1 : ∑ j ∈ Finset.range (J + 1), f₁ j ≤
      (J₁ + 1) * (Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁)) := by
    have h1 : ∑ j ∈ Finset.range (J + 1), f₁ j =
        ∑ j ∈ (Finset.range (J + 1)).filter (fun j => 2 ≤ j ∧ j ≤ J₁),
          (Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁)) := by
      rw [Finset.sum_filter]
    have h2 : (Finset.range (J + 1)).filter (fun j => 2 ≤ j ∧ j ≤ J₁) ⊆ Finset.range (J₁ + 1) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact Finset.mem_range.mpr (by omega)
    rw [h1]
    calc _ ≤ ∑ j ∈ Finset.range (J₁ + 1), (Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁)) :=
          Finset.sum_le_sum_of_subset_of_nonneg h2 (fun j _ _ => hc0)
      _ = (J₁ + 1) * (Real.exp J₁ * E₁ + R * Real.exp ((1 - κ) * J₁)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hr0 : 0 ≤ Real.exp (-(1 / 5 : ℝ)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1 / 5 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hs2 : ∑ j ∈ Finset.range (J + 1), f₂ j ≤
      G * (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ)))) := by
    have h1 : ∑ j ∈ Finset.range (J + 1), f₂ j =
        ∑ j ∈ (Finset.range (J + 1)).filter (fun j => J₁ < j), G * Real.exp (-(1 / 5 : ℝ)) ^ j := by
      rw [Finset.sum_filter]
    have h2 : (Finset.range (J + 1)).filter (fun j => J₁ < j) ⊆ Finset.Ico (J₁ + 1) (J + 1) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      exact Finset.mem_Ico.mpr ⟨by omega, hj.1⟩
    rw [h1, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hG
    calc ∑ j ∈ (Finset.range (J + 1)).filter (fun j => J₁ < j), Real.exp (-(1 / 5 : ℝ)) ^ j
        ≤ ∑ j ∈ Finset.Ico (J₁ + 1) (J + 1), Real.exp (-(1 / 5 : ℝ)) ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg h2 (fun j _ _ => by positivity)
      _ ≤ _ := geom_sum_Ico_le_of_lt_one hr0 hr1
  linarith

/-! ## One height block -/

/-- The near-line constant `51/(200π)`. -/
abbrev nearLineLayerConst : ℝ := 51 / (200 * Real.pi)

/-- The near-line displacement `a = (50/51)(j/λ)L'` for layer `j`. -/
theorem nearLine_layer_facts {lam L' j : ℝ} (hlam : 0 < lam) (hratio : 98 / 100 * lam ≤ L')
    (hj2 : 2 ≤ j) (hjL : j ≤ lam / 100) :
    1 ≤ 50 / 51 * (j / lam) * L' ∧ 50 / 51 * (j / lam) * L' ≤ L' / 100 ∧
      L' / (2 * Real.pi * (50 / 51 * (j / lam) * L')) ≤ nearLineLayerConst * lam ∧
      169 / 200 * j ≤ 22 / 25 * (50 / 51 * (j / lam) * L') := by
  have hL' : 0 < L' := by linarith
  have hr : (98 / 100 : ℝ) ≤ L' / lam := by rw [le_div_iff₀ hlam]; linarith
  have hrew : 50 / 51 * (j / lam) * L' = 50 / 51 * j * (L' / lam) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrew]; nlinarith
  · have : j / lam ≤ 1 / 100 := by rw [div_le_iff₀ hlam]; linarith
    nlinarith
  · have hpi := Real.pi_pos
    have hj0 : 0 < j := by linarith
    have heq : L' / (2 * Real.pi * (50 / 51 * (j / lam) * L')) = 51 * lam / (100 * Real.pi * j) := by
      field_simp
      ring
    calc L' / (2 * Real.pi * (50 / 51 * (j / lam) * L')) = 51 * lam / (100 * Real.pi * j) := heq
      _ ≤ 51 * lam / (200 * Real.pi) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      _ = nearLineLayerConst * lam := by unfold nearLineLayerConst; ring
  · rw [hrew]; nlinarith

/-- The layer count `N_j` of the block `[S, 2S]`. -/
abbrev blockLayerCount (S lam : ℝ) (j : ℕ) : ℝ :=
  ∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 + j / lam < w.re), zeroMult w

/-- **Near-line layers** `2 ≤ j ≤ λ/100`. -/
theorem blockLayerCount_le_nearLine {S T₁ T₂ L' A K : ℝ} {j : ℕ}
    (hS : 20 ≤ S) (hT₁ : S < T₁) (hT₁' : T₁ < S + 1) (hT₂ : 2 * S - 1 < T₂) (hT₂' : T₂ < 2 * S)
    (hlam1 : 1 ≤ Real.log (2 * S)) (hratio : 98 / 100 * Real.log (2 * S) ≤ L')
    (hj2 : 2 ≤ j) (hjL : (j : ℝ) ≤ Real.log (2 * S) / 100) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hD3 : ∀ a : ℝ, 1 ≤ a → a ≤ L' / 100 → ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
      2 * Real.pi * ((a / L') *
        ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L') ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
        (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L') :
    blockLayerCount S (Real.log (2 * S)) j ≤
      (20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
        nearLineLayerConst * Real.log (2 * S) * (K * L')) +
      nearLineLayerConst * Real.log (2 * S) * (S * A) * Real.exp (-(169 / 200 * j)) := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (2 * S) := ⟨_, rfl⟩
  rw [← hlam] at hlam1 hratio hjL ⊢
  have hlam0 : 0 < lam := by linarith
  have hL' : 0 < L' := by linarith
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  obtain ⟨ha1, haL, hcoef, hexp⟩ := nearLine_layer_facts hlam0 hratio hjR hjL
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 50 / 51 * (j / lam) * L' := ⟨_, rfl⟩
  rw [← ha] at ha1 haL hcoef hexp
  have hσ : 1 / 2 + 51 / 50 * (a / L') ≤ 1 / 2 + j / lam := by
    have : 51 / 50 * (a / L') = j / lam := by rw [ha]; field_simp
    linarith
  have hsplit := sum_blockZeros_filter_le_split (σ := 1 / 2 + j / lam)
    (A := S) (B := 2 * S) hT₁.le (by linarith) hT₂'.le
  have hmid := sum_blockZeros_filter_le_nearLine (T₁ := T₁) (T₂ := T₂) (L := L') (a := a)
    (A := A) (K := K) (σ := 1 / 2 + j / lam) (by linarith) (by linarith) hL' (by linarith) hσ
    (hD3 a ha1 haL)
  have hside₁ : (∑ w ∈ blockZeros S T₁, zeroMult w) ≤ 20 * Real.log (180 * (S + 1)) :=
    sum_rectangleZeros_window_le (t := S + 1) (by linarith) le_rfl (by norm_num) hT₁.le
      (by linarith) (by linarith)
  have hside₂ : (∑ w ∈ blockZeros T₂ (2 * S), zeroMult w) ≤ 20 * Real.log (180 * (2 * S)) :=
    sum_rectangleZeros_window_le (t := 2 * S) (by linarith) le_rfl (by norm_num) hT₂'.le
      (by linarith) (by linarith)
  have hE : Real.exp (-(22 / 25 * a)) ≤ Real.exp (-(169 / 200 * (j : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlen : 0 ≤ T₂ - T₁ := by linarith
  have hin : (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L' ≤
      S * A * Real.exp (-(169 / 200 * (j : ℝ))) + K * L' := by
    have h1 : (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) ≤
        S * (A * Real.exp (-(169 / 200 * (j : ℝ)))) := by
      have hTS : T₂ - T₁ ≤ S := by linarith
      have hE0 : 0 ≤ A * Real.exp (-(22 / 25 * a)) := by positivity
      calc (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) ≤ S * (A * Real.exp (-(22 / 25 * a))) :=
            mul_le_mul_of_nonneg_right hTS hE0
        _ ≤ S * (A * Real.exp (-(169 / 200 * (j : ℝ)))) := by gcongr
    linarith
  have hin0 : 0 ≤ (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L' := by positivity
  have hmid' := hmid.trans (mul_le_mul hcoef hin hin0 (by positivity))
  unfold blockLayerCount
  calc (∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 + j / lam < w.re), zeroMult w)
      ≤ _ := hsplit
    _ ≤ 20 * Real.log (180 * (S + 1)) +
          nearLineLayerConst * lam * (S * A * Real.exp (-(169 / 200 * (j : ℝ))) + K * L') +
          20 * Real.log (180 * (2 * S)) := add_le_add (add_le_add hside₁ hmid') hside₂
    _ = _ := by ring

/-- A zero of the residue unit in a block lies left of `Re s = 1`. -/
theorem re_lt_one_of_mem_blockZeros {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {w : ℂ}
    (hw : w ∈ blockZeros A B) : w.re < 1 := by
  rw [mem_blockZeros_iff hAB] at hw
  have hw1 : w ≠ 1 := by
    intro h; have := hw.2.1.1; rw [h] at this; simp at this; linarith
  have hz : riemannZeta w = 0 := by
    by_contra hne
    exact ((Sieve.zetaResidueUnit_ne_zero_iff hw1).2 hne) hw.2.2
  by_contra hcon
  exact (riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon)) hz

/-- **Gabriel layers** `j ≥ 1`. -/
theorem blockLayerCount_le_gabriel {S X K₄ : ℝ} {j : ℕ} (hS : 1 ≤ S) (hj : 1 ≤ j)
    (hlam1 : 1 ≤ Real.log (2 * S)) (hK₄ : 0 ≤ K₄)
    (hX : 2 * S ≤ X - 2) (hX3 : X ≤ 3 * S) (hlogX : 1 + Real.log X ≤ 2 * Real.log (2 * S))
    (hD4 : ∀ u : ℝ, 0 < u → u ≤ 1 / 2 →
      Sieve.zetaLittlewoodZeroCountAbove (1 / 2 + 19 / 20 * u) 4 (X - 2) (1 / 2 + u) ≤
        K₄ / u * X ^ (1 - 6 / 5 * u) * (1 + Real.log X) ^ 2) :
    blockLayerCount S (Real.log (2 * S)) j ≤
      12 * K₄ * S * Real.log (2 * S) ^ 3 * Real.exp (-(6 / 5 * j)) := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (2 * S) := ⟨_, rfl⟩
  rw [← hlam] at hlam1 hlogX ⊢
  have hlam0 : 0 < lam := by linarith
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hR0 : 0 ≤ 12 * K₄ * S * lam ^ 3 * Real.exp (-(6 / 5 * (j : ℝ))) := by positivity
  unfold blockLayerCount
  by_cases hu : (j : ℝ) / lam ≤ 1 / 2
  · have hu0 : 0 < (j : ℝ) / lam := by positivity
    have hcount := (sum_blockZeros_filter_le_gabriel (S := S) (X := X) (u := j / lam)
      hS hX hu0).trans (hD4 _ hu0 hu)
    refine hcount.trans ?_
    have hX0 : 0 < X := by linarith
    have hlX : lam ≤ Real.log X := by
      rw [hlam]; exact Real.log_le_log (by linarith) (by linarith)
    have h1 : (X ^ (6 / 5 * ((j : ℝ) / lam)))⁻¹ ≤ Real.exp (-(6 / 5 * (j : ℝ))) := by
      rw [← Real.rpow_neg hX0.le, Real.rpow_def_of_pos hX0, Real.exp_le_exp]
      have heq : (6 / 5 * ((j : ℝ) / lam)) * lam = 6 / 5 * j := by field_simp
      have hnn : 0 ≤ 6 / 5 * ((j : ℝ) / lam) := by positivity
      nlinarith
    have hXpow : X ^ (1 - 6 / 5 * ((j : ℝ) / lam)) ≤ 3 * S * Real.exp (-(6 / 5 * (j : ℝ))) := by
      rw [Real.rpow_sub hX0, Real.rpow_one, div_eq_mul_inv]
      exact mul_le_mul hX3 h1 (by positivity) (by positivity)
    have hlog2 : (1 + Real.log X) ^ 2 ≤ 4 * lam ^ 2 := by
      have h0 : 0 ≤ 1 + Real.log X := by
        have : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
        linarith
      nlinarith
    have hKu : K₄ / ((j : ℝ) / lam) ≤ K₄ * lam := by
      rw [div_le_iff₀ hu0]
      have : K₄ * lam * ((j : ℝ) / lam) = K₄ * j := by field_simp
      rw [this]
      nlinarith
    calc K₄ / ((j : ℝ) / lam) * X ^ (1 - 6 / 5 * ((j : ℝ) / lam)) * (1 + Real.log X) ^ 2
        ≤ (K₄ * lam) * (3 * S * Real.exp (-(6 / 5 * (j : ℝ)))) * (4 * lam ^ 2) := by
          have hXp0 : 0 ≤ X ^ (1 - 6 / 5 * ((j : ℝ) / lam)) := Real.rpow_nonneg hX0.le _
          have hK0 : 0 ≤ K₄ / ((j : ℝ) / lam) := div_nonneg hK₄ hu0.le
          gcongr
      _ = 12 * K₄ * S * lam ^ 3 * Real.exp (-(6 / 5 * (j : ℝ))) := by ring
  · have hempty : (∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 + j / lam < w.re),
        zeroMult w) = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [Finset.mem_filter] at hw
      exfalso
      have hre1 := re_lt_one_of_mem_blockZeros (by linarith) (by linarith) hw.1
      linarith [hw.2, not_le.mp hu]
    rw [hempty]
    exact hR0

/-- The weighted block sum is at most `e Σ_j e^j N_j`. -/
theorem blockWeight_le_layers {S : ℝ} (hS : 1 ≤ S) (hlam1 : 1 ≤ Real.log (2 * S)) :
    ∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 < w.re),
        zeroMult w * Real.exp (Real.log (2 * S) * (w.re - 1 / 2)) ≤
      Real.exp 1 * ∑ j ∈ Finset.range (⌈Real.log (2 * S)⌉₊ + 1),
        Real.exp j * blockLayerCount S (Real.log (2 * S)) j := by
  classical
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (2 * S) := ⟨_, rfl⟩
  rw [← hlam] at hlam1 ⊢
  have hlam0 : 0 < lam := by linarith
  have hlayers := sum_weight_le_layers (F := (blockZeros S (2 * S)).filter (fun w => 1 / 2 < w.re))
    (m := zeroMult) (lam := lam) (J := ⌈lam⌉₊) hlam0 (fun w _ => zeroMult_nonneg w) (by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hre1 := re_lt_one_of_mem_blockZeros (by linarith) (by linarith) hw.1
      refine ⟨hw.2, ?_⟩
      have hJ' : lam ≤ ⌈lam⌉₊ := Nat.le_ceil lam
      nlinarith)
  refine hlayers.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_)
    (Real.exp_pos 1).le)
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  unfold blockLayerCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w _ _ => zeroMult_nonneg w)
  intro w hw
  rw [Finset.mem_filter, Finset.mem_filter] at hw
  exact Finset.mem_filter.mpr ⟨hw.1.1, hw.2⟩

/-- **The block bound at one scale**, explicit. -/
theorem offLineBlock_le_explicit {S T₁ T₂ L' X A K C₀ K₄ : ℝ} {J₁ : ℕ}
    (hS : 20 ≤ S) (hT₁ : S < T₁) (hT₁' : T₁ < S + 1) (hT₂ : 2 * S - 1 < T₂) (hT₂' : T₂ < 2 * S)
    (hlam1 : 1 ≤ Real.log (2 * S)) (hratio : 98 / 100 * Real.log (2 * S) ≤ L')
    (hJ₁ : 2 ≤ J₁) (hJ₁L : (J₁ : ℝ) ≤ Real.log (2 * S) / 100)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hK₄ : 0 ≤ K₄)
    (hX : 2 * S ≤ X - 2) (hX3 : X ≤ 3 * S) (hlogX : 1 + Real.log X ≤ 2 * Real.log (2 * S))
    (htot : (∑ w ∈ blockZeros S (2 * S), zeroMult w) ≤ C₀ * (2 * S + 4) * Real.log (2 * S + 5))
    (hD3 : ∀ a : ℝ, 1 ≤ a → a ≤ L' / 100 → ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
      2 * Real.pi * ((a / L') *
        ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L') ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
        (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L')
    (hD4 : ∀ u : ℝ, 0 < u → u ≤ 1 / 2 →
      Sieve.zetaLittlewoodZeroCountAbove (1 / 2 + 19 / 20 * u) 4 (X - 2) (1 / 2 + u) ≤
        K₄ / u * X ^ (1 - 6 / 5 * u) * (1 + Real.log X) ^ 2) :
    ∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 < w.re),
        zeroMult w * Real.exp (Real.log (2 * S) * (w.re - 1 / 2)) ≤
      Real.exp 1 * ((1 + Real.exp 1) * (C₀ * (2 * S + 4) * Real.log (2 * S + 5)) +
        (J₁ + 1) * (Real.exp J₁ * (20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
            nearLineLayerConst * Real.log (2 * S) * (K * L')) +
          nearLineLayerConst * Real.log (2 * S) * (S * A) *
            Real.exp ((1 - 169 / 200) * J₁)) +
        12 * K₄ * S * Real.log (2 * S) ^ 3 *
          (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ))))) := by
  refine (blockWeight_le_layers (by linarith) hlam1).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
  have hE₁ : 0 ≤ 20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
      nearLineLayerConst * Real.log (2 * S) * (K * L') := by
    have h1 : 0 ≤ Real.log (180 * (S + 1)) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (180 * (2 * S)) := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ L' := by linarith
    positivity
  have hN₀ : 0 ≤ C₀ * (2 * S + 4) * Real.log (2 * S + 5) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * S + 5 by linarith)
    positivity
  refine layer_sum_le (N := blockLayerCount S (Real.log (2 * S))) (κ := 169 / 200) (by norm_num)
    hN₀ hE₁ (by positivity) (by positivity) (fun j _ => ?_) (fun j hj2 hjJ => ?_)
    (fun j hj _ => ?_)
  · refine le_trans ?_ htot
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun w _ _ => zeroMult_nonneg w)
  · have hjL : (j : ℝ) ≤ Real.log (2 * S) / 100 := by
      have : (j : ℝ) ≤ J₁ := by exact_mod_cast hjJ
      linarith
    exact blockLayerCount_le_nearLine hS hT₁ hT₁' hT₂ hT₂' hlam1 hratio hj2 hjL hA hK hD3
  · exact blockLayerCount_le_gabriel (by linarith) (by omega) hlam1 hK₄ hX hX3 hlogX hD4

/-! ## Size facts in `λ = log 2S` -/

/-- `(11/2) log λ + 1 ≤ λ^{19/400}` and `(11/2) log λ ≤ λ/100` for all large `λ`. -/
theorem eventually_layerCut_facts : ∀ᶠ lam : ℝ in atTop,
    11 / 2 * Real.log lam + 1 ≤ lam ^ (19 / 400 : ℝ) ∧ 11 / 2 * Real.log lam ≤ lam / 100 ∧
      2 + 1 ≤ 11 / 2 * Real.log lam := by
  have h1 := eventually_const_mul_one_add_log_le_rpow (C := 11 / 2 + 1) (ε := 19 / 400)
    (by norm_num)
  have h2 := eventually_const_mul_one_add_log_le_rpow (C := 1100) (ε := 1) (by norm_num)
  have h3 := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (6 / 11 * 3))
  filter_upwards [h1, h2, h3, eventually_ge_atTop (1 : ℝ)] with lam hl1 hl2 hl3 hlam1
  have hlog0 : 0 ≤ Real.log lam := Real.log_nonneg hlam1
  rw [Real.rpow_one] at hl2
  refine ⟨by nlinarith, by nlinarith, by linarith⟩

/-- `C λ⁸ ≤ e^λ/2` for all large `λ`. -/
theorem eventually_poly_le_exp_half (C : ℝ) : ∀ᶠ lam : ℝ in atTop,
    C * lam ^ 8 ≤ Real.exp lam / 2 := by
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * (|C| + 1)) by positivity))
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with lam hl hlam0
  have hE : 0 < Real.exp lam := Real.exp_pos lam
  have h1 : lam ^ 8 < Real.exp lam / (2 * (|C| + 1)) := by
    rw [Real.exp_neg] at hl
    have hpos : 0 < Real.exp lam * (2 * (|C| + 1)) := by positivity
    have h := mul_lt_mul_of_pos_right hl hpos
    have e1 : lam ^ 8 * (Real.exp lam)⁻¹ * (Real.exp lam * (2 * (|C| + 1))) =
        lam ^ 8 * (2 * (|C| + 1)) := by field_simp
    have e2 : 1 / (2 * (|C| + 1)) * (Real.exp lam * (2 * (|C| + 1))) = Real.exp lam := by
      field_simp
    rw [e1, e2] at h
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hp : 0 ≤ lam ^ 8 := by positivity
  calc C * lam ^ 8 ≤ (|C| + 1) * lam ^ 8 := by
        have := le_abs_self C
        nlinarith
    _ ≤ (|C| + 1) * (Real.exp lam / (2 * (|C| + 1))) := by
        exact mul_le_mul_of_nonneg_left h1.le (by positivity)
    _ = Real.exp lam / 2 := by field_simp

/-- The block constant. -/
abbrev offLineBlockConst (A K₄ C₀ : ℝ) : ℝ :=
  Real.exp 1 * ((1 + Real.exp 1) * (6 * C₀) + 1 + nearLineLayerConst * A +
    12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ))))

theorem log_one_eighty_le_six : Real.log 180 ≤ 6 := by
  rw [← Real.log_exp 6]
  refine Real.log_le_log (by norm_num) ?_
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h3 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) h.le 6
  have h4 : (180 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
  linarith

theorem log_block_ends_le {S : ℝ} (hS : 20 ≤ S) (hlam1 : 1 ≤ Real.log (2 * S)) :
    Real.log (180 * (S + 1)) ≤ 7 * Real.log (2 * S) ∧
      Real.log (180 * (2 * S)) ≤ 7 * Real.log (2 * S) := by
  have h180 := log_one_eighty_le_six
  have hmul : Real.log (180 * (2 * S)) = Real.log 180 + Real.log (2 * S) :=
    Real.log_mul (by norm_num) (by linarith)
  have hle : Real.log (180 * (S + 1)) ≤ Real.log (180 * (2 * S)) :=
    Real.log_le_log (by positivity) (by linarith)
  constructor <;> linarith

/-- `(1+e) C₀ (2S + 4) log(2S + 5) ≤ (1+e) 6 C₀ S λ^{19/10}`. -/
theorem blockTotal_le_rpow {S C₀ : ℝ} (hS : 20 ≤ S) (hC₀ : 0 ≤ C₀)
    (hlam1 : 1 ≤ Real.log (2 * S)) :
    C₀ * (2 * S + 4) * Real.log (2 * S + 5) ≤ 6 * C₀ * S * Real.log (2 * S) ^ (19 / 10 : ℝ) := by
  have hlog5 : Real.log (2 * S + 5) ≤ 2 * Real.log (2 * S) := by
    have h : 2 * S + 5 ≤ (2 * S) ^ 2 := by nlinarith
    calc Real.log (2 * S + 5) ≤ Real.log ((2 * S) ^ 2) := Real.log_le_log (by linarith) h
      _ = 2 * Real.log (2 * S) := by rw [Real.log_pow]; push_cast; ring
  have h2 : Real.log (2 * S) ≤ Real.log (2 * S) ^ (19 / 10 : ℝ) := by
    calc Real.log (2 * S) = Real.log (2 * S) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hlam1 (by norm_num)
  have hlog5' : 0 ≤ Real.log (2 * S + 5) := Real.log_nonneg (by linarith)
  calc C₀ * (2 * S + 4) * Real.log (2 * S + 5) ≤ C₀ * (3 * S) * (2 * Real.log (2 * S)) := by
        gcongr; linarith
    _ = 6 * C₀ * S * Real.log (2 * S) := by ring
    _ ≤ 6 * C₀ * S * Real.log (2 * S) ^ (19 / 10 : ℝ) := by gcongr

/-- The mid-range near-line layers are absorbed by `S`. -/
theorem blockNearLow_le {S L' K lam : ℝ} {J₁ : ℕ} (hS : 20 ≤ S) (hlam : lam = Real.log (2 * S))
    (hlam1 : 1 ≤ lam) (hL'0 : 0 ≤ L') (hL' : L' ≤ lam) (hK : 0 ≤ K)
    (hJ₁ : (J₁ : ℝ) ≤ 11 / 2 * Real.log lam)
    (hcut : 11 / 2 * Real.log lam + 1 ≤ lam ^ (19 / 400 : ℝ))
    (hpoly : (280 + nearLineLayerConst * K) * lam ^ 8 ≤ S) :
    ((J₁ : ℝ) + 1) * (Real.exp J₁ * (20 * Real.log (180 * (S + 1)) +
      20 * Real.log (180 * (2 * S)) + nearLineLayerConst * lam * (K * L'))) ≤ S := by
  have hlam0 : 0 < lam := by linarith
  obtain ⟨h1, h2⟩ := log_block_ends_le hS (hlam ▸ hlam1)
  rw [← hlam] at h1 h2
  have hc₁ : 0 ≤ nearLineLayerConst := by unfold nearLineLayerConst; positivity
  have hpowJ : Real.exp J₁ ≤ lam ^ (11 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hlam0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hKL : nearLineLayerConst * lam * (K * L') ≤ nearLineLayerConst * K * lam ^ 2 := by
    have h3 : K * L' ≤ K * lam := mul_le_mul_of_nonneg_left hL' hK
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ nearLineLayerConst * lam)
    calc nearLineLayerConst * lam * (K * L') ≤ nearLineLayerConst * lam * (K * lam) := h4
      _ = nearLineLayerConst * K * lam ^ 2 := by ring
  have hlin : 280 * lam ≤ 280 * lam ^ 2 := by nlinarith
  have hE₁ : 20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
      nearLineLayerConst * lam * (K * L') ≤ (280 + nearLineLayerConst * K) * lam ^ 2 := by
    linarith
  have hE₁0 : 0 ≤ 20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
      nearLineLayerConst * lam * (K * L') := by
    have h5 : 0 ≤ Real.log (180 * (S + 1)) := Real.log_nonneg (by linarith)
    have h6 : 0 ≤ Real.log (180 * (2 * S)) := Real.log_nonneg (by linarith)
    positivity
  have hJ1 : (J₁ : ℝ) + 1 ≤ lam ^ (19 / 400 : ℝ) := by linarith
  have hpow8 : lam ^ (19 / 400 : ℝ) * lam ^ (11 / 2 : ℝ) * lam ^ 2 ≤ lam ^ 8 := by
    rw [show lam ^ 2 = lam ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num, ← Real.rpow_add hlam0,
      ← Real.rpow_add hlam0, show lam ^ 8 = lam ^ (8 : ℝ) by rw [← Real.rpow_natCast]; norm_num]
    exact Real.rpow_le_rpow_of_exponent_le hlam1 (by norm_num)
  have hA0 : 0 ≤ 280 + nearLineLayerConst * K := by positivity
  calc ((J₁ : ℝ) + 1) * (Real.exp J₁ * (20 * Real.log (180 * (S + 1)) +
        20 * Real.log (180 * (2 * S)) + nearLineLayerConst * lam * (K * L')))
      ≤ lam ^ (19 / 400 : ℝ) * (lam ^ (11 / 2 : ℝ) * ((280 + nearLineLayerConst * K) * lam ^ 2)) := by
        gcongr
    _ = (280 + nearLineLayerConst * K) * (lam ^ (19 / 400 : ℝ) * lam ^ (11 / 2 : ℝ) * lam ^ 2) := by
        ring
    _ ≤ (280 + nearLineLayerConst * K) * lam ^ 8 := mul_le_mul_of_nonneg_left hpow8 hA0
    _ ≤ S := hpoly

/-- The near-line layers beyond: `(J₁+1) c₁ λ S A e^{(31/200)J₁} ≤ c₁ A S λ^{19/10}`. -/
theorem blockNearHigh_le {S A lam : ℝ} {J₁ : ℕ} (hS : 0 ≤ S) (hA : 0 ≤ A) (hlam1 : 1 ≤ lam)
    (hJ₁ : (J₁ : ℝ) ≤ 11 / 2 * Real.log lam)
    (hcut : 11 / 2 * Real.log lam + 1 ≤ lam ^ (19 / 400 : ℝ)) :
    ((J₁ : ℝ) + 1) * (nearLineLayerConst * lam * (S * A) * Real.exp ((1 - 169 / 200) * J₁)) ≤
      nearLineLayerConst * A * S * lam ^ (19 / 10 : ℝ) := by
  have hlam0 : 0 < lam := by linarith
  have hc₁ : 0 ≤ nearLineLayerConst := by unfold nearLineLayerConst; positivity
  have hpowJ' : Real.exp ((1 - 169 / 200) * J₁) ≤ lam ^ (341 / 400 : ℝ) := by
    rw [Real.rpow_def_of_pos hlam0]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hJ₁ (by norm_num : (0 : ℝ) ≤ 31 / 200)
    linarith
  have hJ1 : (J₁ : ℝ) + 1 ≤ lam ^ (19 / 400 : ℝ) := by linarith
  have hpow19 : lam ^ (19 / 400 : ℝ) * lam * lam ^ (341 / 400 : ℝ) = lam ^ (19 / 10 : ℝ) := by
    rw [show lam ^ (19 / 400 : ℝ) * lam * lam ^ (341 / 400 : ℝ) =
        lam ^ (19 / 400 : ℝ) * (lam ^ (1 : ℝ) * lam ^ (341 / 400 : ℝ)) by rw [Real.rpow_one]; ring,
      ← Real.rpow_add hlam0, ← Real.rpow_add hlam0]
    norm_num
  calc ((J₁ : ℝ) + 1) * (nearLineLayerConst * lam * (S * A) * Real.exp ((1 - 169 / 200) * J₁))
      ≤ lam ^ (19 / 400 : ℝ) * (nearLineLayerConst * lam * (S * A) * lam ^ (341 / 400 : ℝ)) := by
        gcongr
    _ = nearLineLayerConst * A * S * (lam ^ (19 / 400 : ℝ) * lam * lam ^ (341 / 400 : ℝ)) := by ring
    _ = _ := by rw [hpow19]

/-- The Gabriel layers: `12 K₄ S λ³ r^{J₁+1}/(1−r) ≤ (12K₄/(1−r)) S λ^{19/10}`. -/
theorem blockGabriel_le {S K₄ lam : ℝ} {J₁ : ℕ} (hS : 0 ≤ S) (hK₄ : 0 ≤ K₄) (hlam1 : 1 ≤ lam)
    (hJ₁' : 11 / 2 * Real.log lam < J₁ + 1) :
    12 * K₄ * S * lam ^ 3 *
      (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ)))) ≤
      12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ))) * S * lam ^ (19 / 10 : ℝ) := by
  have hlam0 : 0 < lam := by linarith
  have hr : Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) ≤ lam ^ (-(11 / 10 : ℝ)) := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hlam0]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hr1 : Real.exp (-(1 / 5 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hrpos : 0 < 1 - Real.exp (-(1 / 5 : ℝ)) := by linarith
  have hpow3 : lam ^ 3 * lam ^ (-(11 / 10 : ℝ)) = lam ^ (19 / 10 : ℝ) := by
    rw [show lam ^ 3 = lam ^ (3 : ℝ) by rw [← Real.rpow_natCast]; norm_num, ← Real.rpow_add hlam0]
    norm_num
  calc 12 * K₄ * S * lam ^ 3 *
        (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ))))
      ≤ 12 * K₄ * S * lam ^ 3 * (lam ^ (-(11 / 10 : ℝ)) / (1 - Real.exp (-(1 / 5 : ℝ)))) := by
        gcongr
    _ = 12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ))) * S * (lam ^ 3 * lam ^ (-(11 / 10 : ℝ))) := by
        field_simp
    _ = _ := by rw [hpow3]

/-- **Absorbing the explicit block bound** into `C S λ^{19/10}`. -/
theorem offLineBlock_explicit_le {S L' A K C₀ K₄ : ℝ} {J₁ : ℕ} (hS : 20 ≤ S)
    (hlam1 : 1 ≤ Real.log (2 * S)) (hL'0 : 0 ≤ L') (hL' : L' ≤ Real.log (2 * S))
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hK₄ : 0 ≤ K₄)
    (hJ₁ : (J₁ : ℝ) ≤ 11 / 2 * Real.log (Real.log (2 * S)))
    (hJ₁' : 11 / 2 * Real.log (Real.log (2 * S)) < J₁ + 1)
    (hcut : 11 / 2 * Real.log (Real.log (2 * S)) + 1 ≤ Real.log (2 * S) ^ (19 / 400 : ℝ))
    (hpoly : (280 + nearLineLayerConst * K) * Real.log (2 * S) ^ 8 ≤ S) :
    Real.exp 1 * ((1 + Real.exp 1) * (C₀ * (2 * S + 4) * Real.log (2 * S + 5)) +
        (J₁ + 1) * (Real.exp J₁ * (20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
            nearLineLayerConst * Real.log (2 * S) * (K * L')) +
          nearLineLayerConst * Real.log (2 * S) * (S * A) *
            Real.exp ((1 - 169 / 200) * J₁)) +
        12 * K₄ * S * Real.log (2 * S) ^ 3 *
          (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ))))) ≤
      offLineBlockConst A K₄ C₀ * S * Real.log (2 * S) ^ (19 / 10 : ℝ) := by
  have hS0 : 0 ≤ S := by linarith
  have h1 := blockTotal_le_rpow hS hC₀ hlam1
  have h2 := blockNearLow_le hS rfl hlam1 hL'0 hL' hK hJ₁ hcut hpoly
  have h3 := blockNearHigh_le hS0 hA hlam1 hJ₁ hcut
  have h4 := blockGabriel_le hS0 hK₄ hlam1 hJ₁'
  have h19 : 1 ≤ Real.log (2 * S) ^ (19 / 10 : ℝ) := Real.one_le_rpow hlam1 (by norm_num)
  have hS19 : S ≤ S * Real.log (2 * S) ^ (19 / 10 : ℝ) := le_mul_of_one_le_right hS0 h19
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + Real.exp 1)
  unfold offLineBlockConst
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = S * Real.log (2 * S) ^ (19 / 10 : ℝ) := ⟨_, rfl⟩
  have hsum : (1 + Real.exp 1) * (C₀ * (2 * S + 4) * Real.log (2 * S + 5)) +
      (J₁ + 1) * (Real.exp J₁ * (20 * Real.log (180 * (S + 1)) + 20 * Real.log (180 * (2 * S)) +
          nearLineLayerConst * Real.log (2 * S) * (K * L')) +
        nearLineLayerConst * Real.log (2 * S) * (S * A) * Real.exp ((1 - 169 / 200) * J₁)) +
      12 * K₄ * S * Real.log (2 * S) ^ 3 *
        (Real.exp (-(1 / 5 : ℝ)) ^ (J₁ + 1) / (1 - Real.exp (-(1 / 5 : ℝ)))) ≤
      ((1 + Real.exp 1) * (6 * C₀) + 1 + nearLineLayerConst * A +
        12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ)))) * P := by
    rw [mul_add]
    have e1 : (1 + Real.exp 1) * (6 * C₀ * S * Real.log (2 * S) ^ (19 / 10 : ℝ)) =
        (1 + Real.exp 1) * (6 * C₀) * P := by rw [hP]; ring
    have e3 : nearLineLayerConst * A * S * Real.log (2 * S) ^ (19 / 10 : ℝ) =
        nearLineLayerConst * A * P := by rw [hP]; ring
    have e4 : 12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ))) * S * Real.log (2 * S) ^ (19 / 10 : ℝ) =
        12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ))) * P := by rw [hP]; ring
    rw [e1] at h1'
    rw [e3] at h3
    rw [e4] at h4
    rw [← hP] at hS19
    nlinarith
  calc Real.exp 1 * _ ≤ Real.exp 1 * (((1 + Real.exp 1) * (6 * C₀) + 1 + nearLineLayerConst * A +
        12 * K₄ / (1 - Real.exp (-(1 / 5 : ℝ)))) * P) := mul_le_mul_of_nonneg_left hsum he
    _ = _ := by rw [hP]; ring

/-- **The block bound.** `Σ_{β > 1/2, S ≤ γ ≤ 2S} (2S)^{β − 1/2} ≤ C S (log 2S)^{19/10}` for all large `S`. -/
theorem exists_eventually_offLineBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ S : ℝ in atTop,
      ∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 < w.re),
        zeroMult w * Real.exp (Real.log (2 * S) * (w.re - 1 / 2)) ≤
          C * S * Real.log (2 * S) ^ (19 / 10 : ℝ) := by
  obtain ⟨A, K, hA, hK, hD3ev⟩ := exists_selberg_criticalGate_nearLine_zeroDensity
  obtain ⟨K₄, hK₄, hD4ev⟩ := Sieve.InghamNearHalf.exists_eventually_zeroCountAbove_le_nearHalf
  obtain ⟨C₀, hC₀, htot⟩ := exists_sum_blockZeros_le
  have hr1 : Real.exp (-(1 / 5 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hc₁ : 0 ≤ nearLineLayerConst := by unfold nearLineLayerConst; positivity
  refine ⟨offLineBlockConst A K₄ C₀, ?_, ?_⟩
  · unfold offLineBlockConst
    have : 0 < 1 - Real.exp (-(1 / 5 : ℝ)) := by linarith
    positivity
  have hD3S := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 2)).eventually hD3ev
  have hXt : Tendsto (fun S : ℝ => ⌈2 * S⌉₊ + 2) atTop atTop :=
    (tendsto_add_atTop_nat 2).comp (tendsto_nat_ceil_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have hD4S := hXt.eventually hD4ev
  have hlamt : Tendsto (fun S : ℝ => Real.log (2 * S)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hcutS := hlamt.eventually eventually_layerCut_facts
  have hpolyS := hlamt.eventually (eventually_poly_le_exp_half (280 + nearLineLayerConst * K))
  have hlam15 := hlamt.eventually (eventually_ge_atTop (17 : ℝ))
  filter_upwards [hD3S, hD4S, hcutS, hpolyS, hlam15, eventually_ge_atTop (20 : ℝ)]
    with S hD3 hD4 hcut hpoly hlam hS20
  simp only [id] at hD3 hD4 hcut hpoly hlam
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hD3
  have e1 : 2 * (3 / 2 * S) / 3 = S := by ring
  have e2 : 4 * (3 / 2 * S) / 3 = 2 * S := by ring
  rw [e1] at hT₁
  rw [e2] at hT₂
  have hS0 : 0 < S := by linarith
  obtain ⟨hcut1, hcut2, hcut3⟩ := hcut
  -- the cut `J₁`
  set J₁ : ℕ := ⌊11 / 2 * Real.log (Real.log (2 * S))⌋₊ with hJ₁def
  have hy0 : 0 ≤ 11 / 2 * Real.log (Real.log (2 * S)) := by linarith
  have hJ₁le : (J₁ : ℝ) ≤ 11 / 2 * Real.log (Real.log (2 * S)) := Nat.floor_le hy0
  have hJ₁lt : 11 / 2 * Real.log (Real.log (2 * S)) < J₁ + 1 := Nat.lt_floor_add_one _
  have hJ₁2 : 2 ≤ J₁ := by
    rw [hJ₁def]
    exact Nat.le_floor (by push_cast; linarith)
  -- the length `L' = log(3S/2)`
  have hL'le : Real.log (3 / 2 * S) ≤ Real.log (2 * S) :=
    Real.log_le_log (by positivity) (by linarith)
  have hL'0 : 0 ≤ Real.log (3 / 2 * S) := Real.log_nonneg (by linarith)
  have hratio : 98 / 100 * Real.log (2 * S) ≤ Real.log (3 / 2 * S) := by
    have hsplit : Real.log (2 * S) = Real.log (4 / 3) + Real.log (3 / 2 * S) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
    have h43 : Real.log (4 / 3) ≤ 1 / 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
      linarith
    linarith
  -- the height `X = ⌈2S⌉ + 2`
  set X : ℕ := ⌈2 * S⌉₊ + 2 with hXdef
  have hXlo : 2 * S ≤ (X : ℝ) - 2 := by
    rw [hXdef]; push_cast; linarith [Nat.le_ceil (2 * S)]
  have hXhi : (X : ℝ) ≤ 3 * S := by
    rw [hXdef]; push_cast; linarith [Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * S)]
  have hlogX : 1 + Real.log X ≤ 2 * Real.log (2 * S) := by
    have h1 : Real.log X ≤ Real.log (3 * S) := Real.log_le_log (by linarith) hXhi
    have h2 : Real.log (3 * S) = Real.log (3 / 2) + Real.log (2 * S) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
    have h32 : Real.log (3 / 2) ≤ 1 / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      linarith
    linarith
  have hpoly' : (280 + nearLineLayerConst * K) * Real.log (2 * S) ^ 8 ≤ S := by
    have h := hpoly
    rw [Real.exp_log (by positivity)] at h
    linarith
  have hexpl := offLineBlock_le_explicit (S := S) (T₁ := T₁) (T₂ := T₂) (L' := Real.log (3 / 2 * S))
    (X := X) (A := A) (K := K) (C₀ := C₀) (K₄ := K₄) (J₁ := J₁) hS20 hT₁.1 hT₁.2 hT₂.1 hT₂.2
    (by linarith) hratio hJ₁2 (by linarith) hA.le hK hC₀.le hK₄ hXlo hXhi hlogX
    (htot (by linarith)) hcount hD4
  exact hexpl.trans (offLineBlock_explicit_le hS20 (by linarith) hL'0 hL'le hA.le hK hC₀.le hK₄
    hJ₁le hJ₁lt hcut1 hpoly')

/-! ## Summing the blocks against the Gaussian -/

/-- `e^{−4^j} ≤ 2/16^j`. -/
theorem exp_neg_four_pow_le (j : ℕ) : Real.exp (-((4 : ℝ) ^ j)) ≤ 2 / 16 ^ j := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 ^ j by positivity)
  have h16 : (16 : ℝ) ^ j = ((4 : ℝ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _), h16]
  have hp : 0 ≤ (4 : ℝ) ^ j := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Dyadic Gaussian sum.** For `T ≥ 1` and `k₀ = ⌊log₂ ⌈T⌉⌋ + 1`,
`Σ_k 2^k (k+1)^{19/10} e^{−4^k/T²} ≤ 20 T (k₀ + 1)^{19/10}`. -/
theorem sum_dyadic_gauss_le {T : ℝ} (hT : 1 ≤ T) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) *
      Real.exp (-((4 : ℝ) ^ k / T ^ 2)) ≤
      20 * T * (((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ) := by
  classical
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = Nat.log 2 ⌈T⌉₊ + 1 := ⟨_, rfl⟩
  rw [← hk₀]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((k₀ : ℝ) + 1) ^ (19 / 10 : ℝ) := ⟨_, rfl⟩
  rw [← hc]
  have hT0 : 0 < T := by linarith
  have hn1 : 1 ≤ ⌈T⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hT0).ne'
  have h2k₀ : T ≤ (2 : ℝ) ^ k₀ := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌈T⌉₊
    have h' : (⌈T⌉₊ : ℝ) < (2 : ℝ) ^ k₀ := by rw [hk₀]; exact_mod_cast h
    linarith [Nat.le_ceil T]
  have h2k₀' : (2 : ℝ) ^ k₀ ≤ 4 * T := by
    have h := Nat.pow_log_le_self 2 (show ⌈T⌉₊ ≠ 0 by omega)
    have h' : ((2 : ℝ) ^ (Nat.log 2 ⌈T⌉₊)) ≤ (⌈T⌉₊ : ℝ) := by exact_mod_cast h
    have hceil : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    rw [hk₀, pow_succ]
    linarith
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hpt : ∀ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) *
      Real.exp (-((4 : ℝ) ^ k / T ^ 2)) ≤
      (if k < k₀ then (2 : ℝ) ^ k * c else 0) +
        (if k₀ ≤ k then 8 * T * c * ((2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ k) else 0) := by
    intro k _
    have hnn : 0 ≤ (4 : ℝ) ^ k / T ^ 2 := by positivity
    have he1 : Real.exp (-((4 : ℝ) ^ k / T ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    by_cases hk : k < k₀
    · rw [if_pos hk, if_neg (by omega), add_zero]
      have hkk : ((k : ℝ) + 1) ^ (19 / 10 : ℝ) ≤ c := by
        rw [hc]
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : k + 1 ≤ k₀ + 1))
          (by norm_num)
      calc (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) * Real.exp (-((4 : ℝ) ^ k / T ^ 2))
          ≤ (2 : ℝ) ^ k * c * 1 := by gcongr
        _ = (2 : ℝ) ^ k * c := by ring
    · rw [if_neg hk, if_pos (by omega), zero_add]
      obtain ⟨j, rfl⟩ : ∃ j, k = k₀ + j := ⟨k - k₀, by omega⟩
      have hpow : (2 : ℝ) ^ (k₀ + j) = 2 ^ k₀ * 2 ^ j := pow_add _ _ _
      have hexp : Real.exp (-((4 : ℝ) ^ (k₀ + j) / T ^ 2)) ≤ 2 / 16 ^ j := by
        refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_four_pow_le j)
        have h4 : (4 : ℝ) ^ (k₀ + j) = ((2 : ℝ) ^ k₀) ^ 2 * 4 ^ j := by
          rw [pow_add, ← pow_mul, mul_comm k₀ 2, pow_mul]; norm_num
        rw [h4, neg_le_neg_iff, le_div_iff₀ (by positivity)]
        have : T ^ 2 ≤ ((2 : ℝ) ^ k₀) ^ 2 := pow_le_pow_left₀ hT0.le h2k₀ 2
        have h4j : 0 ≤ (4 : ℝ) ^ j := by positivity
        nlinarith
      have hfac : (((k₀ + j : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ) ≤ c * 4 ^ j := by
        have h1 : (((k₀ + j : ℕ) : ℝ) + 1) ≤ ((k₀ : ℝ) + 1) * ((j : ℝ) + 1) := by
          push_cast; nlinarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        have h2 : ((j : ℝ) + 1) ^ (19 / 10 : ℝ) ≤ 4 ^ j := by
          have h3 : ((j : ℝ) + 1) ^ (19 / 10 : ℝ) ≤ ((j : ℝ) + 1) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
              (by norm_num)
          have h4 : ((j : ℝ) + 1) ^ (2 : ℝ) ≤ 4 ^ j := by
            rw [Real.rpow_two]
            have : ((j : ℝ) + 1) ≤ 2 ^ j := by
              have := Nat.lt_two_pow_self (n := j)
              exact_mod_cast this
            calc ((j : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ j) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
              _ = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          linarith
        calc (((k₀ + j : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ)
            ≤ (((k₀ : ℝ) + 1) * ((j : ℝ) + 1)) ^ (19 / 10 : ℝ) :=
              Real.rpow_le_rpow (by positivity) h1 (by norm_num)
          _ = c * ((j : ℝ) + 1) ^ (19 / 10 : ℝ) := by
              rw [Real.mul_rpow (by positivity) (by positivity), hc]
          _ ≤ c * 4 ^ j := mul_le_mul_of_nonneg_left h2 hc0
      have hhalf : (2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ (k₀ + j) = (1 / 2 : ℝ) ^ j := by
        rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num
      rw [hhalf, hpow]
      calc (2 : ℝ) ^ k₀ * 2 ^ j * (((k₀ + j : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ) *
            Real.exp (-((4 : ℝ) ^ (k₀ + j) / T ^ 2))
          ≤ (4 * T) * 2 ^ j * (c * 4 ^ j) * (2 / 16 ^ j) := by gcongr
        _ = 8 * T * c * ((2 : ℝ) ^ j * 4 ^ j / 16 ^ j) := by ring
        _ = 8 * T * c * (1 / 2 : ℝ) ^ j := by
            congr 1
            rw [← mul_pow, div_eq_mul_inv, ← inv_pow, ← mul_pow]; norm_num
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  have hs1 : ∑ k ∈ Finset.range (K + 1), (if k < k₀ then (2 : ℝ) ^ k * c else 0) ≤ 4 * T * c := by
    have h1 : ∑ k ∈ Finset.range (K + 1), (if k < k₀ then (2 : ℝ) ^ k * c else 0) =
        ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k₀), (2 : ℝ) ^ k * c := by
      rw [Finset.sum_filter]
    have h2 : (Finset.range (K + 1)).filter (fun k => k < k₀) ⊆ Finset.range k₀ := by
      intro k hk; rw [Finset.mem_filter] at hk; exact Finset.mem_range.mpr hk.2
    rw [h1]
    calc _ ≤ ∑ k ∈ Finset.range k₀, (2 : ℝ) ^ k * c :=
          Finset.sum_le_sum_of_subset_of_nonneg h2 (fun k _ _ => by positivity)
      _ = ((2 : ℝ) ^ k₀ - 1) * c := by
          rw [← Finset.sum_mul, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; ring
      _ ≤ 4 * T * c := by nlinarith
  have hs2 : ∑ k ∈ Finset.range (K + 1),
      (if k₀ ≤ k then 8 * T * c * ((2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ k) else 0) ≤ 16 * T * c := by
    have h1 : ∑ k ∈ Finset.range (K + 1),
        (if k₀ ≤ k then 8 * T * c * ((2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ k) else 0) =
        8 * T * c * (2 : ℝ) ^ k₀ *
          ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k₀ ≤ k), (1 / 2 : ℝ) ^ k := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    have h2 : (Finset.range (K + 1)).filter (fun k => k₀ ≤ k) ⊆ Finset.Ico k₀ (K + 1) := by
      intro k hk; rw [Finset.mem_filter, Finset.mem_range] at hk
      exact Finset.mem_Ico.mpr ⟨hk.2, hk.1⟩
    have hgeo := geom_sum_Ico_le_of_lt_one (m := k₀) (n := K + 1) (x := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
    have h3 : ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k₀ ≤ k), (1 / 2 : ℝ) ^ k ≤
        (1 / 2 : ℝ) ^ k₀ / (1 - 1 / 2) :=
      (Finset.sum_le_sum_of_subset_of_nonneg h2 (fun k _ _ => by positivity)).trans hgeo
    rw [h1]
    have h4 : (2 : ℝ) ^ k₀ * ((1 / 2 : ℝ) ^ k₀ / (1 - 1 / 2)) = 2 := by
      rw [← mul_div_assoc, ← mul_pow]; norm_num
    have h5 : 0 ≤ 8 * T * c * (2 : ℝ) ^ k₀ := by positivity
    calc 8 * T * c * (2 : ℝ) ^ k₀ *
          ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k₀ ≤ k), (1 / 2 : ℝ) ^ k
        ≤ 8 * T * c * (2 : ℝ) ^ k₀ * ((1 / 2 : ℝ) ^ k₀ / (1 - 1 / 2)) :=
          mul_le_mul_of_nonneg_left h3 h5
      _ = 8 * T * c * ((2 : ℝ) ^ k₀ * ((1 / 2 : ℝ) ^ k₀ / (1 - 1 / 2))) := by ring
      _ = 16 * T * c := by rw [h4]; ring
  linarith

/-- `⌊log₂ n⌋ ≤ log n / log 2`. -/
theorem nat_log_two_le_log_div {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have h' : ((2 : ℝ) ^ (Nat.log 2 n)) ≤ (n : ℝ) := by exact_mod_cast h
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

/-- The block of a zero: `2^k ≤ γ < 2^{k+1}` for `k = ⌊log₂ ⌊γ⌋⌋`. -/
theorem two_pow_le_and_lt {y : ℝ} (hy : 1 ≤ y) :
    (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊) ≤ y ∧ y < 2 * (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊) := by
  have hfl : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have h1 := Nat.pow_log_le_self 2 (show ⌊y⌋₊ ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊y⌋₊
  have h1' : ((2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊)) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
  have h2' : (⌊y⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1) := by exact_mod_cast h2
  have hfl1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hfl2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  rw [pow_succ] at h2'
  constructor <;> linarith

/-- The weighted block sum. -/
abbrev blockWeight (S : ℝ) : ℝ :=
  ∑ w ∈ (blockZeros S (2 * S)).filter (fun w => 1 / 2 < w.re),
    zeroMult w * Real.exp (Real.log (2 * S) * (w.re - 1 / 2))

/-- **Fibering the zero sum into dyadic blocks.** -/
theorem offLineWeight_le_blocks {T Y : ℝ} (hY : 1 ≤ Y) :
    ∑ w ∈ (blockZeros 1 Y).filter (fun w => 1 / 2 < w.re),
      zeroMult w * (Real.exp ((w.re - 1 / 2) * Real.log w.im) * Real.exp (-(w.im ^ 2 / T ^ 2))) ≤
      ∑ k ∈ Finset.range (Nat.log 2 ⌊Y⌋₊ + 1),
        Real.exp (-((4 : ℝ) ^ k / T ^ 2)) * blockWeight ((2 : ℝ) ^ k) := by
  classical
  set F := (blockZeros 1 Y).filter (fun w => 1 / 2 < w.re) with hF
  have hmaps : ∀ w ∈ F, Nat.log 2 ⌊w.im⌋₊ ∈ Finset.range (Nat.log 2 ⌊Y⌋₊ + 1) := by
    intro w hw
    rw [hF, Finset.mem_filter, mem_blockZeros_iff hY] at hw
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right ?_))
    exact Nat.floor_le_floor hw.1.2.1.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun k _ => ?_
  have hsub : F.filter (fun w => Nat.log 2 ⌊w.im⌋₊ = k) ⊆
      (blockZeros ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k)).filter (fun w => 1 / 2 < w.re) := by
    intro w hw
    rw [Finset.mem_filter, hF, Finset.mem_filter, mem_blockZeros_iff hY] at hw
    obtain ⟨⟨⟨hre, him, hz⟩, hre2⟩, hk⟩ := hw
    obtain ⟨h1, h2⟩ := two_pow_le_and_lt him.1
    rw [hk] at h1 h2
    rw [Finset.mem_filter, mem_blockZeros_iff (by linarith [pow_pos (two_pos : (0 : ℝ) < 2) k])]
    exact ⟨⟨hre, ⟨h1, h2.le⟩, hz⟩, hre2⟩
  have hpt : ∀ w ∈ F.filter (fun w => Nat.log 2 ⌊w.im⌋₊ = k),
      zeroMult w * (Real.exp ((w.re - 1 / 2) * Real.log w.im) * Real.exp (-(w.im ^ 2 / T ^ 2))) ≤
      Real.exp (-((4 : ℝ) ^ k / T ^ 2)) *
        (zeroMult w * Real.exp (Real.log (2 * (2 : ℝ) ^ k) * (w.re - 1 / 2))) := by
    intro w hw
    rw [Finset.mem_filter, hF, Finset.mem_filter, mem_blockZeros_iff hY] at hw
    obtain ⟨⟨⟨hre, him, hz⟩, hre2⟩, hk⟩ := hw
    obtain ⟨h1, h2⟩ := two_pow_le_and_lt him.1
    rw [hk] at h1 h2
    have hpos : 0 < (2 : ℝ) ^ k := by positivity
    have hlog : Real.log w.im ≤ Real.log (2 * (2 : ℝ) ^ k) :=
      Real.log_le_log (by linarith) h2.le
    have he1 : Real.exp ((w.re - 1 / 2) * Real.log w.im) ≤
        Real.exp (Real.log (2 * (2 : ℝ) ^ k) * (w.re - 1 / 2)) := by
      apply Real.exp_le_exp.mpr
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hlog (by linarith)
    have he2 : Real.exp (-(w.im ^ 2 / T ^ 2)) ≤ Real.exp (-((4 : ℝ) ^ k / T ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have h4 : (4 : ℝ) ^ k ≤ w.im ^ 2 := by
        have : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]
        exact pow_le_pow_left₀ hpos.le h1 2
      have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
      rcases hT2.lt_or_eq with hT2 | hT2
      · have := div_le_div_of_nonneg_right h4 hT2.le
        linarith
      · rw [← hT2]; simp
    have hm := zeroMult_nonneg w
    calc zeroMult w * (Real.exp ((w.re - 1 / 2) * Real.log w.im) * Real.exp (-(w.im ^ 2 / T ^ 2)))
        ≤ zeroMult w * (Real.exp (Real.log (2 * (2 : ℝ) ^ k) * (w.re - 1 / 2)) *
            Real.exp (-((4 : ℝ) ^ k / T ^ 2))) := by gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => by
    have := zeroMult_nonneg w; positivity)

/-- Low blocks are bounded by the block sum up to `2^{kk}`. -/
theorem blockWeight_le_low {k kk : ℕ} (hk : k < kk) :
    blockWeight ((2 : ℝ) ^ k) ≤
      ∑ w ∈ (blockZeros 1 ((2 : ℝ) ^ kk)).filter (fun w => 1 / 2 < w.re),
        zeroMult w * Real.exp (Real.log ((2 : ℝ) ^ kk) * (1 / 2)) := by
  classical
  unfold blockWeight
  have hpk : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h2k : 2 * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ kk := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hk
  have hkk1 : (1 : ℝ) ≤ (2 : ℝ) ^ kk := one_le_pow₀ (by norm_num)
  have hsub : (blockZeros ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k)).filter (fun w => 1 / 2 < w.re) ⊆
      (blockZeros 1 ((2 : ℝ) ^ kk)).filter (fun w => 1 / 2 < w.re) := by
    intro w hw
    rw [Finset.mem_filter, mem_blockZeros_iff (by linarith)] at hw
    rw [Finset.mem_filter, mem_blockZeros_iff hkk1]
    exact ⟨⟨hw.1.1, ⟨by linarith [hw.1.2.1.1], by linarith [hw.1.2.1.2]⟩, hw.1.2.2⟩, hw.2⟩
  refine le_trans (Finset.sum_le_sum fun w hw => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => by
      have := zeroMult_nonneg w; positivity))
  rw [Finset.mem_filter] at hw
  have hre1 := re_lt_one_of_mem_blockZeros (by linarith) (by linarith) hw.1
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (zeroMult_nonneg w)
  have hl1 : Real.log (2 * (2 : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ kk) :=
    Real.log_le_log (by positivity) h2k
  have hl0 : 0 ≤ Real.log (2 * (2 : ℝ) ^ k) := Real.log_nonneg (by linarith)
  have hx : w.re - 1 / 2 ≤ 1 / 2 := by linarith
  have hx0 : 0 ≤ w.re - 1 / 2 := by linarith [hw.2]
  calc Real.log (2 * (2 : ℝ) ^ k) * (w.re - 1 / 2) ≤ Real.log ((2 : ℝ) ^ kk) * (w.re - 1 / 2) :=
        mul_le_mul_of_nonneg_right hl1 hx0
    _ ≤ Real.log ((2 : ℝ) ^ kk) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hx (le_trans hl0 hl1)

/-- **The Gaussian-weighted off-line zero sum is `o(T log² T)`.** For every `ε > 0`, for all large
`T` and every `Y ≥ 1`,
`Σ_{β > 1/2, 1 ≤ γ ≤ Y} m_ρ γ^{β−1/2} e^{−γ²/T²} ≤ ε T (log T)²`. -/
theorem eventually_offLineWeight_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Y : ℝ, 1 ≤ Y →
      ∑ w ∈ (blockZeros 1 Y).filter (fun w => 1 / 2 < w.re),
        zeroMult w * (Real.exp ((w.re - 1 / 2) * Real.log w.im) *
          Real.exp (-(w.im ^ 2 / T ^ 2))) ≤ ε * T * Real.log T ^ 2 := by
  classical
  obtain ⟨C, hC, hBL⟩ := exists_eventually_offLineBlock_le
  obtain ⟨S₀, hS₀⟩ := hBL.exists_forall_of_atTop
  -- the low blocks
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, kk = Nat.log 2 ⌈max S₀ 1⌉₊ + 1 := ⟨_, rfl⟩
  have hkkS : max S₀ 1 ≤ (2 : ℝ) ^ kk := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌈max S₀ 1⌉₊
    have h' : (⌈max S₀ 1⌉₊ : ℝ) < (2 : ℝ) ^ kk := by rw [hkk]; exact_mod_cast h
    linarith [Nat.le_ceil (max S₀ 1)]
  set B₀ : ℝ := ∑ w ∈ (blockZeros 1 ((2 : ℝ) ^ kk)).filter (fun w => 1 / 2 < w.re),
    zeroMult w * Real.exp (Real.log ((2 : ℝ) ^ kk) * (1 / 2)) with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun w _ => by
    have := zeroMult_nonneg w; positivity
  -- the eventual size facts
  have hlogt := Real.tendsto_log_atTop
  have hlarge : ∀ᶠ T : ℝ in atTop, kk * B₀ + 180 * C * T * Real.log T ^ (19 / 10 : ℝ) ≤
      ε * T * Real.log T ^ 2 := by
    have h1 := hlogt.eventually (eventually_ge_atTop ((360 * C / ε + 1) ^ (10 : ℝ)))
    have h2 := hlogt.eventually (eventually_ge_atTop (1 : ℝ))
    have h3 : ∀ᶠ T : ℝ in atTop, 2 * (kk * B₀) ≤ ε * T := by
      filter_upwards [eventually_ge_atTop (2 * (kk * B₀) / ε)] with T hT
      have := (div_le_iff₀ hε).mp hT
      linarith
    filter_upwards [h1, h2, h3, eventually_ge_atTop (1 : ℝ)] with T hT1 hT2 hT3 hT
    have hL0 : 0 < Real.log T := by linarith
    have hpow : 360 * C / ε ≤ Real.log T ^ (1 / 10 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hT1 (by norm_num : (0 : ℝ) ≤ 1 / 10)
      rw [← Real.rpow_mul (by positivity)] at h
      norm_num at h
      linarith
    have hsplit : Real.log T ^ (2 : ℝ) = Real.log T ^ (19 / 10 : ℝ) * Real.log T ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hL2 : Real.log T ^ 2 = Real.log T ^ (2 : ℝ) := by rw [Real.rpow_two]
    have hp19 : 0 ≤ Real.log T ^ (19 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
    have hp1 : 1 ≤ Real.log T ^ 2 := by nlinarith
    have hmain : 360 * C * T * Real.log T ^ (19 / 10 : ℝ) ≤ ε * T * Real.log T ^ 2 := by
      rw [hL2, hsplit]
      have := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ ε * T * Real.log T ^ (19 / 10 : ℝ))
      have e : ε * T * Real.log T ^ (19 / 10 : ℝ) * (360 * C / ε) = 360 * C * T * Real.log T ^ (19 / 10 : ℝ) := by
        field_simp
      nlinarith
    have hTL : ε * T ≤ ε * T * Real.log T ^ 2 := le_mul_of_one_le_right (by positivity) hp1
    nlinarith
  have hk₀ : ∀ᶠ T : ℝ in atTop, ((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) + 1 ≤ 3 * Real.log T := by
    have h1 := hlogt.eventually (eventually_ge_atTop (20 : ℝ))
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with T hT1 hT
    have hn : 1 ≤ ⌈T⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
    have hlog := nat_log_two_le_log_div hn
    have hceil : (⌈T⌉₊ : ℝ) ≤ 2 * T := by linarith [Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ T)]
    have hlog2 : Real.log (⌈T⌉₊ : ℝ) ≤ Real.log 2 + Real.log T := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) hceil
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2' : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have hdiv : Real.log (⌈T⌉₊ : ℝ) / Real.log 2 ≤ 2 * (Real.log 2 + Real.log T) := by
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 ≤ Real.log 2 + Real.log T := by linarith
      nlinarith
    push_cast
    linarith
  filter_upwards [hlarge, hk₀, eventually_ge_atTop (1 : ℝ)] with T hTlarge hTk₀ hT Y hY
  refine (offLineWeight_le_blocks (T := T) hY).trans ?_
  set K := Nat.log 2 ⌊Y⌋₊ with hK
  have hpt : ∀ k ∈ Finset.range (K + 1),
      Real.exp (-((4 : ℝ) ^ k / T ^ 2)) * blockWeight ((2 : ℝ) ^ k) ≤
        (if k < kk then B₀ else 0) +
          C * ((2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) * Real.exp (-((4 : ℝ) ^ k / T ^ 2))) := by
    intro k _
    have he1 : Real.exp (-((4 : ℝ) ^ k / T ^ 2)) ≤ 1 := by
      have : 0 ≤ (4 : ℝ) ^ k / T ^ 2 := by positivity
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hBW0 : 0 ≤ blockWeight ((2 : ℝ) ^ k) := Finset.sum_nonneg fun w _ => by
      have := zeroMult_nonneg w; positivity
    have hsec : 0 ≤ C * ((2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) *
        Real.exp (-((4 : ℝ) ^ k / T ^ 2))) := by positivity
    by_cases hk : k < kk
    · rw [if_pos hk]
      have hlow := blockWeight_le_low hk
      rw [← hB₀] at hlow
      have : Real.exp (-((4 : ℝ) ^ k / T ^ 2)) * blockWeight ((2 : ℝ) ^ k) ≤ 1 * B₀ :=
        mul_le_mul he1 hlow hBW0 zero_le_one
      linarith
    · rw [if_neg hk, zero_add]
      have h2k : S₀ ≤ (2 : ℝ) ^ k := by
        have h1 : (2 : ℝ) ^ kk ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith [le_max_left S₀ 1]
      have hblk := hS₀ ((2 : ℝ) ^ k) h2k
      have hlog : Real.log (2 * (2 : ℝ) ^ k) ≤ (k : ℝ) + 1 := by
        rw [← pow_succ', Real.log_pow]
        have := Real.log_two_lt_d9
        push_cast
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hlog0 : 0 ≤ Real.log (2 * (2 : ℝ) ^ k) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith)
      have hpow : Real.log (2 * (2 : ℝ) ^ k) ^ (19 / 10 : ℝ) ≤ ((k : ℝ) + 1) ^ (19 / 10 : ℝ) :=
        Real.rpow_le_rpow hlog0 hlog (by norm_num)
      have hblk' : blockWeight ((2 : ℝ) ^ k) ≤ C * (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) := by
        refine hblk.trans ?_
        gcongr
      calc Real.exp (-((4 : ℝ) ^ k / T ^ 2)) * blockWeight ((2 : ℝ) ^ k)
          ≤ Real.exp (-((4 : ℝ) ^ k / T ^ 2)) * (C * (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_left hblk' (Real.exp_pos _).le
        _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs1 : ∑ k ∈ Finset.range (K + 1), (if k < kk then B₀ else 0) ≤ kk * B₀ := by
    rw [← Finset.sum_filter]
    calc ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < kk), B₀
        = ((Finset.range (K + 1)).filter (fun k => k < kk)).card * B₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ kk * B₀ := by
          refine mul_le_mul_of_nonneg_right ?_ hB₀0
          have : (Finset.range (K + 1)).filter (fun k => k < kk) ⊆ Finset.range kk := by
            intro k hk; rw [Finset.mem_filter] at hk; exact Finset.mem_range.mpr hk.2
          have h := Finset.card_le_card this
          rw [Finset.card_range] at h
          exact_mod_cast h
  have hs2 := sum_dyadic_gauss_le hT K
  have hk₀' : (((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ) ≤
      9 * Real.log T ^ (19 / 10 : ℝ) := by
    have h0 : 0 ≤ ((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) + 1 := by positivity
    calc (((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ)
        ≤ (3 * Real.log T) ^ (19 / 10 : ℝ) := Real.rpow_le_rpow h0 hTk₀ (by norm_num)
      _ = 3 ^ (19 / 10 : ℝ) * Real.log T ^ (19 / 10 : ℝ) :=
          Real.mul_rpow (by norm_num) (by linarith [h0, hTk₀])
      _ ≤ 9 * Real.log T ^ (19 / 10 : ℝ) := by
          have h3 : (3 : ℝ) ^ (19 / 10 : ℝ) ≤ 9 := by
            calc (3 : ℝ) ^ (19 / 10 : ℝ) ≤ 3 ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 9 := by norm_num
          have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT
          exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hL0 _)
  have hs2' : C * ∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ (19 / 10 : ℝ) *
      Real.exp (-((4 : ℝ) ^ k / T ^ 2)) ≤ 180 * C * T * Real.log T ^ (19 / 10 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hs2 hC
    have h2 : 20 * T * (((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) ^ (19 / 10 : ℝ) ≤
        20 * T * (9 * Real.log T ^ (19 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hk₀' (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hC
    nlinarith
  linarith

end RHTower
