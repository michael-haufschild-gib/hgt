import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleModeMeetsTheZerosOnlyAtTheHorizon

/-!
# The zeros see every atomic vector through its Möbius horizons

Write the conventional coefficients `x_n = √n y_n` of an atomic vector `y` on `1 ≤ n ≤ N` as a
Dirichlet convolution `x = a * 1`, `a = x * μ`. Regrouping `n = dk`
(`sum_divisorSum_mul_cpow`),

`Σ_{n≤N} x_n n^{-s} = Σ_{d≤N} a_d d^{-s} X_{⌊N/d⌋}(s)`,   `X_M(s) = Σ_{k≤M} k^{-s}`,

and each partial zeta sum is `ζ(s) − B_{⌊N/d⌋}(s)`. At a nontrivial zero both `ρ` and `1 − ρ`
annihilate `ζ`, so the two Dirichlet factors of Weil's zero-side summand are exactly minus the
**Möbius horizon** `H_a(s) = Σ_{d≤N} a_d d^{-s} B_{⌊N/d⌋}(s)` (`Wsummand_zetaExtension`).

* **Horizon law for every vector** (`weilQuad_atomicTest_eq_tsum_mobiusHorizon`): for every
  C² compact atom, every horizon and every real coefficient vector,
  `Q(f_y) = Re Σ_ρ m_ρ ĝ(γ_ρ) conj ĝ(conj γ_ρ) · H_a(1−ρ) H_a(ρ)`, `a = (√n y_n) * μ`.

The zeros read an atomic test only through the Euler–Maclaurin boundaries of the horizons
`⌊N/d⌋` of its Möbius transform. Short Möbius transforms (the conductor modes) see only a few
boundaries, all at depth `≍ N`; the pole mode is `a = δ₁`.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri Zeta23

/-! ### Regrouping a convolution with `1` -/

/-- Multiples of `d` in `[1, N]` are `d k`, `1 ≤ k ≤ ⌊N/d⌋`. -/
theorem sum_Icc_filter_dvd {M : Type*} [AddCommMonoid M] {d : ℕ} (hd : 1 ≤ d) (N : ℕ)
    (F : ℕ → M) :
    ∑ n ∈ (Icc 1 N).filter (d ∣ ·), F n = ∑ k ∈ Icc 1 (N / d), F (d * k) := by
  refine Finset.sum_nbij' (fun n => n / d) (fun k => d * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, hN⟩, hdn⟩ := hn
    simp only [mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd h1 hdn) hd, Nat.div_le_div_right hN⟩
  · intro k hk
    simp only [mem_Icc] at hk
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
      dvd_mul_right d k⟩
    exact (Nat.mul_le_mul_left d hk.2).trans (Nat.mul_div_le N d)
  · intro n hn
    simp only [mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro k _
    exact Nat.mul_div_cancel_left k (by omega)
  · intro n hn
    simp only [mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- For `1 ≤ n ≤ N` the divisors of `n` are the divisors of `n` in `[1, N]`. -/
theorem sum_divisors_eq_sum_Icc_ite {M : Type*} [AddCommMonoid M] {n N : ℕ}
    (hn : n ∈ Icc 1 N) (f : ℕ → M) :
    ∑ d ∈ n.divisors, f d = ∑ d ∈ Icc 1 N, if d ∣ n then f d else 0 := by
  rw [← sum_filter]
  obtain ⟨h1, hN⟩ := mem_Icc.mp hn
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hdn, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn h1, (Nat.le_of_dvd h1 hdn).trans hN⟩, hdn⟩
  · rintro ⟨-, hdn⟩
    exact ⟨hdn, by omega⟩

/-- **Regrouping** `Σ_{n≤N} (a*1)(n) n^{-s} = Σ_{d≤N} a_d d^{-s} X_{⌊N/d⌋}(s)`. -/
theorem sum_divisorSum_mul_cpow (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    ∑ n ∈ Icc 1 N, (∑ d ∈ n.divisors, a d) * (n : ℂ) ^ (-s) =
      ∑ d ∈ Icc 1 N, a d * (d : ℂ) ^ (-s) * RHTower.dirichletPoly (N / d) s := by
  have h1 : ∀ n ∈ Icc 1 N, (∑ d ∈ n.divisors, a d) * (n : ℂ) ^ (-s) =
      ∑ d ∈ Icc 1 N, if d ∣ n then a d * (n : ℂ) ^ (-s) else 0 := by
    intro n hn
    rw [sum_mul, sum_divisors_eq_sum_Icc_ite hn]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  rw [← sum_filter, sum_Icc_filter_dvd hd1, RHTower.dirichletPoly, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, natCast_mul_natCast_cpow]
  ring

/-! ### The Möbius horizon -/

/-- The **Möbius horizon** `H_a(s) = Σ_{d≤N} a_d d^{-s} B_{⌊N/d⌋}(s)`. -/
def mobiusHorizon (N : ℕ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ) ^ (-s) * horizonBoundary (N / d) s

/-- At a zero of `ζ` with `Re s > 0`, the convolution sum is minus the Möbius horizon. -/
theorem sum_divisorSum_mul_cpow_eq_neg_mobiusHorizon (a : ℕ → ℝ) (N : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∑ n ∈ Icc 1 N, ((∑ d ∈ n.divisors, a d : ℝ) : ℂ) * (n : ℂ) ^ (-s) =
      -mobiusHorizon N a s := by
  have h := sum_divisorSum_mul_cpow (fun d => (a d : ℂ)) N s
  push_cast
  rw [h, mobiusHorizon, ← sum_neg_distrib]
  refine sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
  have hq : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
  rw [dirichletPoly_eq_neg_horizonBoundary hq hs hs1 hz]
  ring

/-- The atomic coefficients `y_n = (Σ_{d∣n} a_d)/√n` of the convolution `a * 1`. -/
def zetaExtensionCoeff (a : ℕ → ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, a d) * poleModeCoeff n

/-- At the spectral point of `ρ`, the Dirichlet factor is the convolution sum at `1 − ρ`. -/
theorem dirichletPoly_zetaExtension_gammaOf (a : ℕ → ℝ) (N : ℕ) (ρ : ℂ) :
    dirichletPoly N (zetaExtensionCoeff a) (gammaOf ρ) =
      ∑ n ∈ Icc 1 N, ((∑ d ∈ n.divisors, a d : ℝ) : ℂ) * (n : ℂ) ^ (-(1 - ρ)) := by
  rw [dirichletPoly_gammaOf]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [zetaExtensionCoeff, Complex.ofReal_mul, poleModeCoeff_eq_exp hn1, mul_assoc,
    ← Complex.exp_add, natCast_cpow_neg_eq_exp hn1]
  congr 2
  ring

/-- `conj (Σ c_n n^{-conj s}) = Σ c_n n^{-s}` for real weights. -/
theorem conj_sum_real_mul_cpow_conj (c : ℕ → ℝ) (N : ℕ) (s : ℂ) :
    conj (∑ n ∈ Icc 1 N, (c n : ℂ) * (n : ℂ) ^ (-conj s)) =
      ∑ n ∈ Icc 1 N, (c n : ℂ) * (n : ℂ) ^ (-s) := by
  rw [map_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [map_mul, Complex.conj_ofReal, natCast_cpow_neg_eq_exp hn1, natCast_cpow_neg_eq_exp hn1,
    ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal]

/-- The conjugate Dirichlet factor is the convolution sum at `ρ`. -/
theorem conj_dirichletPoly_zetaExtension_conj_gammaOf (a : ℕ → ℝ) (N : ℕ) (ρ : ℂ) :
    conj (dirichletPoly N (zetaExtensionCoeff a) (conj (gammaOf ρ))) =
      ∑ n ∈ Icc 1 N, ((∑ d ∈ n.divisors, a d : ℝ) : ℂ) * (n : ℂ) ^ (-ρ) := by
  rw [conj_gammaOf, dirichletPoly_zetaExtension_gammaOf, sub_sub_cancel,
    conj_sum_real_mul_cpow_conj (fun n => ∑ d ∈ n.divisors, a d)]

/-- **The zero-side summand of every convolution vector** at a nontrivial zero. -/
theorem Wsummand_zetaExtension {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a : ℕ → ℝ) (N : ℕ) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    zetaZeroConfig.Wsummand (cx (atomicTest N (zetaExtensionCoeff a) g))
        (cx (atomicTest N (zetaExtensionCoeff a) g)) ρ =
      (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (mobiusHorizon N a (1 - ρ) * mobiusHorizon N a ρ) := by
  obtain ⟨hz, h0, h1, hz', h0', h1', -⟩ := nontrivialZero_facts hρ
  rw [Wsummand_atomicTest zetaZeroConfig hg hgc, dirichletPoly_zetaExtension_gammaOf,
    conj_dirichletPoly_zetaExtension_conj_gammaOf,
    sum_divisorSum_mul_cpow_eq_neg_mobiusHorizon a N h0' h1' hz',
    sum_divisorSum_mul_cpow_eq_neg_mobiusHorizon a N h0 h1 hz]
  ring

/-! ### Every atomic vector is a convolution vector -/

/-- The Möbius transform `a = (√n y_n) * μ` of an atomic coefficient vector. -/
def atomicMobiusTransform (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ p ∈ d.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ) *
    (Real.sqrt p.2 * y p.2)

theorem zetaExtensionCoeff_atomicMobiusTransform (y : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    zetaExtensionCoeff (atomicMobiusTransform y) n = y n := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := atomicMobiusTransform y) (g := fun m => Real.sqrt m * y m)).mpr
    (fun m _ => rfl) n (by omega)
  have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  rw [zetaExtensionCoeff, hinv, poleModeCoeff]
  field_simp

theorem atomicTest_zetaExtension_atomicMobiusTransform (N : ℕ) (y : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N (zetaExtensionCoeff (atomicMobiusTransform y)) g = atomicTest N y g := by
  funext u
  unfold atomicTest
  refine sum_congr rfl fun n hn => ?_
  rw [zetaExtensionCoeff_atomicMobiusTransform y (mem_Icc.mp hn).1]

/-- **Horizon law for every atomic vector.** For every C² compact atom `g`, every horizon and
every real coefficient vector `y`, Weil's form is the zero sum of the bump factor against the
two Möbius horizons of `a = (√n y_n) * μ`. -/
theorem weilQuad_atomicTest_eq_tsum_mobiusHorizon {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (y : ℕ → ℝ) :
    weilQuad (atomicTest N y g) =
      (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (mobiusHorizon N (atomicMobiusTransform y) (1 - ρ) *
          mobiusHorizon N (atomicMobiusTransform y) ρ)).re := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  set a := atomicMobiusTransform y
  rw [← atomicTest_zetaExtension_atomicMobiusTransform N y g,
    LogCells.weilQuad_eq_zetaW (contDiff_atomicTest hg N (zetaExtensionCoeff a))
      (hasCompactSupport_atomicTest hgsupp N (zetaExtensionCoeff a)), ZeroConfig.W]
  congr 1
  refine tsum_congr fun ρ => ?_
  exact Wsummand_zetaExtension hg.continuous hgc a N ρ.property

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
