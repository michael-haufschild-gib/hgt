import GaloisForLFunctions.RHTower.ZetaAFETransfer
import GaloisForLFunctions.RHTower.CarrierLineSup

/-!
# A square-root vertical bound for zeta near `Re s = 1`

The Euler--Maclaurin approximation with cutoff `ceil(1+‖s‖)` gives a deliberately
coarse but summability-compatible bound on `Re s >= 3/4`, provided `s` stays a
positive distance from the pole at `1`.  The exponent `1/2<1` is the feature
needed for the rectangular shifted-zeta normal-convergence argument.
-/

open Complex

namespace RHTower

noncomputable section

/-- On `Re s>=1/2`, the length-`N` Dirichlet polynomial is bounded by the
square-root telescope. -/
theorem norm_dirichletPoly_le_two_sqrt
    (N : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖dirichletPoly N s‖ ≤ 2 * Real.sqrt N := by
  unfold dirichletPoly
  calc
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤
        ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hnRone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hnRpos, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hnRone (by linarith)
    _ ≤ 2 * Real.sqrt N := sum_rpow_neg_half_le N

/-- The Euler--Maclaurin pole term is bounded by `sqrt N / d` when the
evaluation point stays distance at least `d` from `1`. -/
theorem norm_emPole_le_sqrt_div
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 3 / 4 ≤ s.re)
    {d : ℝ} (hd : 0 < d) (hsep : d ≤ ‖s - 1‖) :
    ‖emPole N s‖ ≤ Real.sqrt N / d := by
  rw [emPole, norm_div]
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hNRone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ‖(N : ℂ) ^ (1 - s)‖ ≤ Real.sqrt N := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hNRpos, Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hNRone
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact div_le_div₀ (Real.sqrt_nonneg _) hpow hd hsep

/-- The Euler--Maclaurin remainder at cutoff `N>=1+‖s‖` is at most
`(4/3)sqrt N` throughout `Re s>=3/4`. -/
theorem emRemainderBudget_le_sqrt
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 3 / 4 ≤ s.re)
    (hsize : 1 + ‖s‖ ≤ (N : ℝ)) :
    ‖s‖ * (N : ℝ) ^ (-s.re) / s.re ≤ (4 / 3 : ℝ) * Real.sqrt N := by
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hNRone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hspos : 0 < s.re := by linarith
  have hnormN : ‖s‖ ≤ (N : ℝ) := by linarith
  have hpow : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hNRone (by linarith)
  have hprod : ‖s‖ * (N : ℝ) ^ (-s.re) ≤ Real.sqrt N := by
    calc
      ‖s‖ * (N : ℝ) ^ (-s.re) ≤
          (N : ℝ) * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by gcongr
      _ = (N : ℝ) ^ (1 / 4 : ℝ) := by
        calc
          (N : ℝ) * (N : ℝ) ^ (-(3 / 4 : ℝ)) =
              (N : ℝ) ^ ((1 : ℝ) + (-(3 / 4 : ℝ))) := by
                rw [Real.rpow_add hNRpos, Real.rpow_one]
          _ = (N : ℝ) ^ (1 / 4 : ℝ) := by
            congr 1
            norm_num
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNRone (by norm_num)
      _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow]
  calc
    ‖s‖ * (N : ℝ) ^ (-s.re) / s.re ≤ Real.sqrt N / (3 / 4 : ℝ) :=
      div_le_div₀ (Real.sqrt_nonneg _) hprod (by norm_num) hs
    _ = (4 / 3 : ℝ) * Real.sqrt N := by ring

/-- **Square-root vertical zeta bound.**  On `Re s>=3/4`, away from the pole
by `d>0`, zeta grows at most like `sqrt(‖s‖+2)`. -/
theorem norm_riemannZeta_le_sqrt_norm_add_two
    {s : ℂ} (hs : 3 / 4 ≤ s.re) {d : ℝ} (hd : 0 < d)
    (hsep : d ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤
      (2 + 1 / d + 4 / 3) * Real.sqrt (‖s‖ + 2) := by
  let N : ℕ := Nat.ceil (1 + ‖s‖)
  have hxnonneg : 0 ≤ 1 + ‖s‖ := by positivity
  have hsize : 1 + ‖s‖ ≤ (N : ℝ) := Nat.le_ceil _
  have hNreal : (1 : ℝ) ≤ 1 + ‖s‖ := by
    linarith [norm_nonneg s]
  have hN : 1 ≤ N := by
    exact_mod_cast le_trans hNreal hsize
  have hNupper : (N : ℝ) ≤ ‖s‖ + 2 := by
    have h := (Nat.ceil_lt_add_one hxnonneg).le
    dsimp [N]
    convert h using 1
    ring
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  have hAFE := zeta_norm_le_afe hN hspos hs1
  have hD : ‖dirichletPoly N s‖ ≤ 2 * Real.sqrt N :=
    norm_dirichletPoly_le_two_sqrt N (by linarith)
  have hP : ‖emPole N s‖ ≤ Real.sqrt N / d :=
    norm_emPole_le_sqrt_div hN hs hd hsep
  have hR : ‖s‖ * (N : ℝ) ^ (-s.re) / s.re ≤
      (4 / 3 : ℝ) * Real.sqrt N :=
    emRemainderBudget_le_sqrt hN hs hsize
  have hsqrt : Real.sqrt N ≤ Real.sqrt (‖s‖ + 2) :=
    Real.sqrt_le_sqrt hNupper
  calc
    ‖riemannZeta s‖ ≤
        ‖dirichletPoly N s‖ + ‖emPole N s‖ +
          ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := hAFE
    _ ≤ 2 * Real.sqrt N + Real.sqrt N / d +
        (4 / 3 : ℝ) * Real.sqrt N := by linarith
    _ = (2 + 1 / d + 4 / 3) * Real.sqrt N := by ring
    _ ≤ (2 + 1 / d + 4 / 3) * Real.sqrt (‖s‖ + 2) := by
      gcongr

/-- Pole-term square-root bound down to the half-plane `Re s >= 1/2`. -/
theorem norm_emPole_le_sqrt_div_half
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {d : ℝ} (hd : 0 < d) (hsep : d ≤ ‖s - 1‖) :
    ‖emPole N s‖ ≤ Real.sqrt N / d := by
  rw [emPole, norm_div]
  have hNRpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hNRone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ‖(N : ℂ) ^ (1 - s)‖ ≤ Real.sqrt N := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hNRpos, Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hNRone
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact div_le_div₀ (Real.sqrt_nonneg _) hpow hd hsep

/-- Euler--Maclaurin remainder bound down to `Re s >= 1/2`. -/
theorem emRemainderBudget_le_two_sqrt
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hsize : 1 + ‖s‖ ≤ (N : ℝ)) :
    ‖s‖ * (N : ℝ) ^ (-s.re) / s.re ≤ 2 * Real.sqrt N := by
  have hNRpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hNRone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hspos : 0 < s.re := by linarith
  have hnormN : ‖s‖ ≤ (N : ℝ) := by linarith
  have hpow : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hNRone (by linarith)
  have hprod : ‖s‖ * (N : ℝ) ^ (-s.re) ≤ Real.sqrt N := by
    calc
      ‖s‖ * (N : ℝ) ^ (-s.re) ≤
          (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) =
              (N : ℝ) ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
                rw [Real.rpow_add hNRpos, Real.rpow_one]
          _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
            congr 1
            ring
      _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow]
  calc
    ‖s‖ * (N : ℝ) ^ (-s.re) / s.re ≤ Real.sqrt N / (1 / 2 : ℝ) :=
      div_le_div₀ (Real.sqrt_nonneg _) hprod (by norm_num) hs
    _ = 2 * Real.sqrt N := by ring

/-- Square-root vertical zeta bound on `Re s >= 1/2`, uniformly away from
the pole at `1`. -/
theorem norm_riemannZeta_le_sqrt_norm_add_two_half
    {s : ℂ} (hs : 1 / 2 ≤ s.re) {d : ℝ} (hd : 0 < d)
    (hsep : d ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤
      (2 + 1 / d + 2) * Real.sqrt (‖s‖ + 2) := by
  let N : ℕ := Nat.ceil (1 + ‖s‖)
  have hxnonneg : 0 ≤ 1 + ‖s‖ := by positivity
  have hsize : 1 + ‖s‖ ≤ (N : ℝ) := Nat.le_ceil _
  have hNreal : (1 : ℝ) ≤ 1 + ‖s‖ := by
    linarith [norm_nonneg s]
  have hN : 1 ≤ N := by
    exact_mod_cast le_trans hNreal hsize
  have hNupper : (N : ℝ) ≤ ‖s‖ + 2 := by
    have h := (Nat.ceil_lt_add_one hxnonneg).le
    dsimp [N]
    convert h using 1
    ring
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  have hAFE := zeta_norm_le_afe hN hspos hs1
  have hD : ‖dirichletPoly N s‖ ≤ 2 * Real.sqrt N :=
    norm_dirichletPoly_le_two_sqrt N hs
  have hP : ‖emPole N s‖ ≤ Real.sqrt N / d :=
    norm_emPole_le_sqrt_div_half hN hs hd hsep
  have hR : ‖s‖ * (N : ℝ) ^ (-s.re) / s.re ≤ 2 * Real.sqrt N :=
    emRemainderBudget_le_two_sqrt hN hs hsize
  have hsqrt : Real.sqrt N ≤ Real.sqrt (‖s‖ + 2) :=
    Real.sqrt_le_sqrt hNupper
  calc
    ‖riemannZeta s‖ ≤
        ‖dirichletPoly N s‖ + ‖emPole N s‖ +
          ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := hAFE
    _ ≤ 2 * Real.sqrt N + Real.sqrt N / d + 2 * Real.sqrt N := by
      linarith
    _ = (2 + 1 / d + 2) * Real.sqrt N := by ring
    _ ≤ (2 + 1 / d + 2) * Real.sqrt (‖s‖ + 2) := by
      gcongr

end

end RHTower
