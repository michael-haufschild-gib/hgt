import GaloisForLFunctions.ArithmeticGaugeTheory.TheMajorArcsOfTheShells

/-!
# The short shells have no conductor

The level-`q` Dirichlet average of the shell part keeps the shells `n = km + j` with `q ∣ j`
(`sum_shellPart_dirichletGauge`, `shellPair_survives_iff`). This file applies it to short kernels.

* **Short kernels have short shells** (`shell_short_of_kernel_short`). If `G(u) = 0` for `|u| ≥ 2/N`
  and `N ≥ 6`, a shell coefficient with `n ≤ N` vanishes unless `|n − km| ≤ 2`. This is the range of
  the atomic Weil kernel at overlap ratio `c ≤ 2` for profiles of unit width.
* **They have no conductor** (`sum_shellPart_dirichletGauge_eq_zero_of_short`,
  `sum_shellPart_dirichletGauge_eq_zero_of_kernel_short`). For every level `q ≥ 3` the Dirichlet
  average of these shells is zero; level `2` has only the principal character.

So up to overlap `c = 2` no finite gauge subgroup sees the shells. Repaying them through conductors
`q ∣ j` is empty, and the sign of the complete form there is a property of the trivial point alone: it
is decided by the pole, the archimedean terms and the gauge charge of `0`, with no singular series to
lean on.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

variable (K N : ℕ) (a x : ℕ → ℂ) (G : ℝ → ℂ)

/-- **Short kernels have short shells.** If `G` vanishes for `|u| ≥ 2/N` and `N ≥ 6`, then a nonzero
shell coefficient with `n ≤ N` has `|n − km| ≤ 2`. -/
theorem shell_short_of_kernel_short (hN : 6 ≤ N) (hG : ∀ u : ℝ, 2 / (N : ℝ) ≤ |u| → G u = 0)
    {k m n : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnN : n ≤ N)
    (h : shellCoeff a x G k m n ≠ 0) : n ≤ k * m + 2 ∧ k * m ≤ n + 2 := by
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnNr : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hkm : (1 : ℝ) ≤ (k : ℝ) * m := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  -- The lag is `log(n/(km))`.
  have hlag : Real.log n - Real.log m - Real.log k = Real.log ((n : ℝ) / (k * m)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  -- A long shell has lag at least `2/N`, where the kernel vanishes.
  have hzero : 2 / (N : ℝ) ≤ |Real.log ((n : ℝ) / (k * m))| → shellCoeff a x G k m n = 0 := by
    intro hlong
    rw [shellCoeff]
    split_ifs
    · rfl
    · rw [hlag, hG _ hlong, mul_zero]
  by_contra hshort
  rw [not_and_or] at hshort
  refine h (hzero ?_)
  have hN0 : (0 : ℝ) < N := by linarith
  rcases hshort with hlt | hlt
  · -- `n ≥ km + 3`: `log(n/(km)) ≥ 1 − km/n ≥ 3/n ≥ 2/N`.
    have h3 : (k : ℝ) * m + 3 ≤ n := by exact_mod_cast (by omega : k * m + 3 ≤ n)
    have hlog := Real.one_sub_inv_le_log_of_pos (x := (n : ℝ) / (k * m)) (by positivity)
    rw [inv_div] at hlog
    have hbound : 2 / (N : ℝ) ≤ 1 - (k : ℝ) * m / n := by
      have e : 1 - (k : ℝ) * m / n = ((n : ℝ) - k * m) / n := by field_simp
      rw [e, div_le_div_iff₀ hN0 (by positivity)]
      nlinarith
    exact (hbound.trans hlog).trans (le_abs_self _)
  · -- `km ≥ n + 3`: `log(km/n) ≥ 1 − n/(km) ≥ 2/N`.
    have h3 : (n : ℝ) + 3 ≤ (k : ℝ) * m := by exact_mod_cast (by omega : n + 3 ≤ k * m)
    have hlog := Real.one_sub_inv_le_log_of_pos (x := (k : ℝ) * m / n) (by positivity)
    rw [inv_div] at hlog
    have hbound : 2 / (N : ℝ) ≤ 1 - (n : ℝ) / (k * m) := by
      have e : 1 - (n : ℝ) / (k * m) = ((k : ℝ) * m - n) / (k * m) := by field_simp
      rw [e, div_le_div_iff₀ hN0 (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) * m - n - 3)
        (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]
    have hneg : Real.log ((n : ℝ) / (k * m)) = -Real.log ((k : ℝ) * m / n) := by
      rw [← Real.log_inv, inv_div]
    rw [hneg, abs_neg]
    exact (hbound.trans hlog).trans (le_abs_self _)

variable {q : ℕ} [NeZero q]

/-- **Short shells have no conductor.** If every nonzero shell has `|n − km| ≤ 2`, the level-`q`
Dirichlet average of the shell part vanishes for every `q ≥ 3`. -/
theorem sum_shellPart_dirichletGauge_eq_zero_of_short (hq : 3 ≤ q) (ha : CoprimeSupported q a)
    (hx : CoprimeSupported q x)
    (hshort : ∀ k m n, k ∈ Icc 1 K → m ∈ Icc 1 N → n ∈ Icc 1 N → shellCoeff a x G k m n ≠ 0 →
      n ≤ k * m + 2 ∧ k * m ≤ n + 2) :
    ∑ χ : DirichletCharacter ℂ q,
        shellPart K N (gaugeTransform (dirichletGauge χ) a) (gaugeTransform (dirichletGauge χ) x) G =
      0 := by
  rw [sum_shellPart_dirichletGauge K N a x G ha hx]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun k hk => sum_eq_zero fun m hm =>
    sum_eq_zero fun n hn => ?_)
  split_ifs with hcong
  · by_contra h0
    obtain ⟨h1, h2⟩ := hshort k m n hk hm hn h0
    have hne : n ≠ k * m := fun he => h0 (by rw [shellCoeff, if_pos he])
    rw [ZMod.natCast_eq_natCast_iff] at hcong
    -- `q` divides the nonzero gap `|n − km| ≤ 2`.
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdvd : q ∣ k * m - n := (Nat.modEq_iff_dvd' hlt.le).mp hcong.symm
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · have hdvd : q ∣ n - k * m := (Nat.modEq_iff_dvd' hgt.le).mp hcong
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  · rfl

/-- **Up to overlap two the shells have no conductor.** For a kernel vanishing at `|u| ≥ 2/N`, `N ≥ 6`,
and every level `q ≥ 3`, the Dirichlet average of the shell part is zero. -/
theorem sum_shellPart_dirichletGauge_eq_zero_of_kernel_short (hq : 3 ≤ q) (hN : 6 ≤ N)
    (hG : ∀ u : ℝ, 2 / (N : ℝ) ≤ |u| → G u = 0) (ha : CoprimeSupported q a)
    (hx : CoprimeSupported q x) :
    ∑ χ : DirichletCharacter ℂ q,
        shellPart K N (gaugeTransform (dirichletGauge χ) a) (gaugeTransform (dirichletGauge χ) x) G =
      0 :=
  sum_shellPart_dirichletGauge_eq_zero_of_short K N a x G hq ha hx fun _ _ _ hk hm hn h =>
    shell_short_of_kernel_short N a x G hN hG (mem_Icc.mp hk).1 (mem_Icc.mp hm).1
      (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 h

end GaloisForLFunctions.ArithmeticGaugeTheory
