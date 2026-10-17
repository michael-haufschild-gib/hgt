import GaloisForLFunctions.BezoutValuationIncidence.BezoutSuccessorQuadraticFormAndDirichletEnergySplit

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar IV: Simultaneous Selberg–Möbius Diagonalization, Wall 11 Spectral Separation, and the Universal `1/2`-Decorrelation Law

This module proves that the Bézout unitary coprime quadratic form
`Q_Bez(N, c) = ∑_{d₁, d₂ ∈ [1, N], gcd(d₁, d₂) = 1} c(d₁) c(d₂) / (d₁ d₂)`
arising from the asymptotic main term of the Bézout successor correlation `∑_{k=1}^M s_{N,c}(k) s_{N,c}(k+1)`
is **simultaneously diagonalized** in the exact same Selberg multiples-coordinates
`Y_{N,c}(e) = selbergMultiplesCoord N c e = ∑_{d ≤ N, e ∣ d} c(d)/d`
as the classical Selberg quadratic form `Q_Sel(N, c) = selbergTotientDiagonalForm N c`, with diagonal
eigenvalue `μ(e)` in place of Euler's totient `φ(e)`:
* `bezoutCoprimeQuadraticForm_eq_moebius_diagonal`:
  `Q_Bez(N, c) = ∑_{e=1}^N μ(e) Y_{N,c}(e)²`.
* `selbergSubBezoutQuadraticForm_eq_Icc_two`:
  Universal cancellation of the `e = 1` harmonic-pole mode `Y_{N,c}(1)²` between `Q_Sel` and `Q_Bez`
  (`φ(1) - μ(1) = 1 - 1 = 0`), even off `ker P`:
  `Q_Sel(N, c) - Q_Bez(N, c) = ∑_{e=2}^N (φ(e) - μ(e)) Y_{N,c}(e)²`.
* `totient_sub_moebiusReal_prime` & `wall11_totient_degeneracy_broken_by_bezout`:
  At every prime `p`, `φ(p) - μ(p) = (p - 1) - (-1) = p` recovers the exact prime weight without the
  totient `-1` defect. Moreover, whereas Selberg's totient weight is degenerate at Wall 11
  (`φ(4) = φ(6) = 2`), the Bézout–Dirichlet eigenvalue strictly separates `4 = 2²` from `6 = 2 · 3`:
  `φ(4) - μ(4) = 2 ≠ 1 = φ(6) - μ(6)`.
* `two_mul_moebiusReal_le_totient`, `bezoutCoprimeQuadraticForm_le_selberg`, &
  `two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero`:
  For every integer `e ≥ 2`, `2 μ(e) ≤ φ(e)` (with unique sharp equality at `e = 6 = 2 · 3` where
  `2 μ(6) = 2 = φ(6)`) and `1 ≤ φ(e) - μ(e)`. Consequently, on `ker P` (`finiteHarmonicSum N c = 0`),
  the Bézout successor form satisfies the **Universal `1/2`-Decorrelation Law**
  `2 * Q_Bez(N, c) ≤ Q_Sel(N, c)`,
  and the asymptotic additive Dirichlet energy density satisfies the **Universal Coercivity Law**
  `Q_Sel(N, c) ≤ 2 * (Q_Sel(N, c) - Q_Bez(N, c))`.
-/

/-! ## §1. Simultaneous Selberg–Möbius Diagonalization of the Bézout Unitary Coprime Form -/

/-- For any `n ≥ 1`, summing `moebiusReal e` over `e ∈ n.divisors` yields `if n = 1 then 1 else 0`. -/
theorem sum_divisors_moebiusReal_eq_ite_one {n : ℕ} (hn : 1 ≤ n) :
    ∑ e ∈ n.divisors, moebiusReal e = if n = 1 then 1 else 0 := by
  by_cases hn1 : n = 1
  · subst hn1
    unfold moebiusReal
    simp
  · rw [if_neg hn1]
    exact sum_divisors_moebiusReal_eq_zero (by omega)

/-- The Bézout unitary coprime quadratic form on `[1, N]`:
`Q_Bez(N, c) = ∑_{d₁, d₂ ∈ [1, N], gcd(d₁, d₂) = 1} c(d₁) c(d₂) / (d₁ d₂)`. -/
def bezoutCoprimeQuadraticForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    (if Nat.Coprime p.1 p.2 then 1 else (0 : ℝ)) *
      (c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))

/-- Pairwise expansion of the coprime kernel via Möbius divisor summation over `gcd(m, n)`. -/
theorem coprime_kernel_eq_sum_moebiusReal (c : ℕ → ℝ) {m n : ℕ} (hm : 1 ≤ m) (_hn : 1 ≤ n) :
    (if Nat.Coprime m n then 1 else (0 : ℝ)) * (c m / (m : ℝ)) * (c n / (n : ℝ)) =
      ∑ e ∈ (Nat.gcd m n).divisors, moebiusReal e * ((c m / (m : ℝ)) * (c n / (n : ℝ))) := by
  have hgcd : 1 ≤ Nat.gcd m n := Nat.gcd_pos_of_pos_left _ hm
  rw [← Finset.sum_mul, sum_divisors_moebiusReal_eq_ite_one hgcd]
  by_cases hcop : Nat.Coprime m n
  · rw [if_pos hcop]
    ring
  · rw [if_neg hcop]
    ring

/-- **Exact Simultaneous Selberg–Möbius Diagonalization of `bezoutCoprimeQuadraticForm`
(`bezoutCoprimeQuadraticForm_eq_moebius_diagonal`):**
For every `N : ℕ` and `c : ℕ → ℝ`, `bezoutCoprimeQuadraticForm N c` is diagonal in the **exact same**
Selberg multiples-coordinates `selbergMultiplesCoord N c e = ∑_{d ≤ N, e ∣ d} c(d)/d` as
`selbergTotientDiagonalForm N c`, with diagonal eigenvalue `μ(e)` in place of `φ(e)`:
`Q_Bez(N, c) = ∑_{e=1}^N μ(e) Y_{N,c}(e)²`. -/
theorem bezoutCoprimeQuadraticForm_eq_moebius_diagonal (N : ℕ) (c : ℕ → ℝ) :
    bezoutCoprimeQuadraticForm N c =
      ∑ e ∈ Finset.Icc 1 N, moebiusReal e * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  classical
  unfold bezoutCoprimeQuadraticForm selbergMultiplesCoord
  have hS : ∀ m ∈ Finset.Icc 1 N, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hexp : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      (if Nat.Coprime p.1 p.2 then 1 else (0 : ℝ)) *
        (c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ)) =
        ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          moebiusReal e * ((c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact coprime_kernel_eq_sum_moebiusReal c (hS _ hp1) (hS _ hp2)
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ∧ e ∈ (Nat.gcd p.1 p.2).divisors ↔
        p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧
          e ∈ (Finset.Icc 1 N).biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      have hp1_pos := hS _ hp1
      exact Nat.mem_divisors.mpr ⟨hd1, by omega⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem, biUnion_divisors_Icc_eq_Icc]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) =
      ((Finset.Icc 1 N).filter (fun m => e ∣ m)) ×ˢ ((Finset.Icc 1 N).filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

/-! ## §2. Universal Pole Cancellation, Wall 11 Spectral Separation (`4` vs `6`), and Prime Recovery -/

/-- **Universal Cancellation of the `e = 1` Harmonic Pole Mode Between `Q_Sel` and `Q_Bez`:**
Because `φ(1) = μ(1) = 1`, for **every** `N ≥ 1` and **every** `c : ℕ → ℝ` (even off `ker P`!),
the `e = 1` harmonic-pole mode `Y_{N,c}(1)²` cancels identically out of
`selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c`:
`Q_Sel(N, c) - Q_Bez(N, c) = ∑_{e=2}^N (φ(e) - μ(e)) Y_{N,c}(e)²`. -/
theorem selbergSubBezoutQuadraticForm_eq_Icc_two {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c =
      ∑ e ∈ Finset.Icc 2 N,
        ((Nat.totient e : ℝ) - moebiusReal e) * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  rw [selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm_eq_moebius_diagonal,
    ← Finset.sum_sub_distrib]
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  have hmu1 : moebiusReal 1 = 1 := by
    unfold moebiusReal
    simp
  simp only [Nat.totient_one, Nat.cast_one, hmu1, one_mul, sub_self, zero_add]
  refine Finset.sum_congr rfl fun e _ => by ring

/-- **Exact Prime Weight Recovery (`totient_sub_moebiusReal_prime`):**
At every prime `p`, the `-1` defect in Euler's totient `φ(p) = p - 1` is cancelled by `μ(p) = -1`,
so the Bézout–Dirichlet eigenvalue `φ(p) - μ(p)` equals `p` exactly! -/
theorem totient_sub_moebiusReal_prime {p : ℕ} (hp : Nat.Prime p) :
    (Nat.totient p : ℝ) - moebiusReal p = (p : ℝ) := by
  unfold moebiusReal
  rw [Nat.totient_prime hp, ArithmeticFunction.moebius_apply_prime hp,
    Nat.cast_sub hp.pos]
  push_cast
  ring

/-- **Wall 11 Spectral Separation (`4 = 2²` vs `6 = 2 · 3`):**
Whereas the classical Selberg totient weight is blind to the difference between `e = 4` and `e = 6`
(`φ(4) = φ(6) = 2`), the Bézout–Dirichlet eigenvalue `φ(e) - μ(e)` strictly separates `e = 4` from
`e = 6`: `φ(4) - μ(4) = 2 ≠ 1 = φ(6) - μ(6)`. -/
theorem wall11_totient_degeneracy_broken_by_bezout :
    Nat.totient 4 = 2 ∧ Nat.totient 6 = 2 ∧
      (Nat.totient 4 : ℝ) - moebiusReal 4 = 2 ∧
      (Nat.totient 6 : ℝ) - moebiusReal 6 = 1 := by
  have htot4 : Nat.totient 4 = 2 := by decide
  have htot6 : Nat.totient 6 = 2 := by decide
  have hmu4 : moebiusReal 4 = 0 := by
    have hnot : ¬ Squarefree 4 := by
      intro hsq
      exact absurd (hsq 2 (by norm_num : 2 * 2 ∣ 4)) (by decide)
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
    norm_num
  have hmu6 : moebiusReal 6 = 1 := by
    unfold moebiusReal
    have hcop : Nat.Coprime 2 3 := by decide
    have hmul : μ (2 * 3) = μ 2 * μ 3 :=
      ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hcop
    change ((μ (2 * 3) : ℤ) : ℝ) = 1
    rw [hmul, ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  refine ⟨htot4, htot6, ?_, ?_⟩
  · rw [htot4, hmu4]; norm_num
  · rw [htot6, hmu6]; norm_num

/-! ## §3. The Universal `1/2`-Decorrelation Law on `ker P` (Sharp at `e = 6`) -/

/-- For every `e : ℕ`, `moebiusReal e ^ 2 ≤ 1` and `moebiusReal e ≤ 1`. -/
theorem moebiusReal_le_one (e : ℕ) :
    moebiusReal e ^ (2 : ℕ) ≤ 1 ∧ moebiusReal e ≤ 1 := by
  have hsq : moebiusReal e ^ (2 : ℕ) ≤ 1 := by
    unfold moebiusReal
    have h := ArithmeticFunction.moebius_sq (n := e)
    by_cases hsf : Squarefree e
    · rw [if_pos hsf] at h
      have hcast : ((μ e : ℤ) : ℝ) ^ (2 : ℕ) = (((μ e ^ (2 : ℕ) : ℤ) : ℝ)) := by push_cast; ring
      rw [hcast, h]
      norm_num
    · rw [if_neg hsf] at h
      have hcast : ((μ e : ℤ) : ℝ) ^ (2 : ℕ) = (((μ e ^ (2 : ℕ) : ℤ) : ℝ)) := by push_cast; ring
      rw [hcast, h]
      norm_num
  refine ⟨hsq, ?_⟩
  nlinarith [sq_nonneg (moebiusReal e - 1)]

/-- **Universal `1/2`-Spectral Gap (`two_mul_moebiusReal_le_totient`):**
For EVERY integer `e ≥ 2`, `2 * μ(e) ≤ φ(e)` (with sharp equality at `e = 6 = 2 * 3`), and hence
`1 ≤ φ(e) - μ(e)`. -/
theorem two_mul_moebiusReal_le_totient {e : ℕ} (he : 2 ≤ e) :
    2 * moebiusReal e ≤ (Nat.totient e : ℝ) ∧
      1 ≤ (Nat.totient e : ℝ) - moebiusReal e := by
  by_cases he2 : e = 2
  · subst he2
    have hmu2 : moebiusReal 2 = -1 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      norm_num
    rw [Nat.totient_prime Nat.prime_two, hmu2]
    norm_num
  · have he3 : 2 < e := by omega
    have htot_pos : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
    have htot_even : 2 ∣ Nat.totient e := even_iff_two_dvd.mp (Nat.totient_even he3)
    have htot_ge2 : 2 ≤ Nat.totient e := Nat.le_of_dvd htot_pos htot_even
    have htot_real : (2 : ℝ) ≤ (Nat.totient e : ℝ) := by exact_mod_cast htot_ge2
    have hmu_le1 : moebiusReal e ≤ 1 := (moebiusReal_le_one e).2
    constructor <;> linarith

/-- **Universal Positive-Semidefiniteness of `Q_Sel - Q_Bez` (`bezoutCoprimeQuadraticForm_le_selberg`):**
For every `N ≥ 1` and every weight `c : ℕ → ℝ` (even off `ker P`!),
`bezoutCoprimeQuadraticForm N c ≤ selbergTotientDiagonalForm N c`. -/
theorem bezoutCoprimeQuadraticForm_le_selberg {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    bezoutCoprimeQuadraticForm N c ≤ selbergTotientDiagonalForm N c := by
  have hdiff := selbergSubBezoutQuadraticForm_eq_Icc_two hN c
  have hnonneg : 0 ≤ ∑ e ∈ Finset.Icc 2 N,
      ((Nat.totient e : ℝ) - moebiusReal e) * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
    refine Finset.sum_nonneg fun e he => ?_
    have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
    have hgap := (two_mul_moebiusReal_le_totient he2).2
    exact mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- **The Universal `1/2`-Decorrelation Law on `ker P`
(`two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero`):**
For every `N ≥ 1` and every `ker P` sieve weight `c` (`finiteHarmonicSum N c = 0`), the
Successor-Node Bézout quadratic form is at most **one-half** of the Same-Node Selberg quadratic form:
`2 * Q_Bez(N, c) ≤ Q_Sel(N, c)`,
and consequently the asymptotic additive Dirichlet energy density satisfies the strict coercivity law
`Q_Sel(N, c) ≤ 2 * (Q_Sel(N, c) - Q_Bez(N, c))`. -/
theorem two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) :
    2 * bezoutCoprimeQuadraticForm N c ≤ selbergTotientDiagonalForm N c ∧
      selbergTotientDiagonalForm N c ≤
        2 * (selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c) := by
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hY1 : selbergMultiplesCoord N c 1 = 0 := by
    rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum, hker]
  have hSel : selbergTotientDiagonalForm N c =
      ∑ e ∈ Finset.Icc 2 N, (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
    unfold selbergTotientDiagonalForm
    rw [hIcc, Finset.sum_insert (by simp), hY1]
    ring
  have hBez : bezoutCoprimeQuadraticForm N c =
      ∑ e ∈ Finset.Icc 2 N, moebiusReal e * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
    rw [bezoutCoprimeQuadraticForm_eq_moebius_diagonal, hIcc, Finset.sum_insert (by simp), hY1]
    ring
  have hle : 2 * bezoutCoprimeQuadraticForm N c ≤ selbergTotientDiagonalForm N c := by
    rw [hBez, hSel, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
    have hgap := (two_mul_moebiusReal_le_totient he2).1
    have hsq : 0 ≤ (selbergMultiplesCoord N c e) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  exact ⟨hle, by linarith⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
