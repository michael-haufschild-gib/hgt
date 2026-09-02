import GaloisForLFunctions.HTGeometry.PoincareSeriesCoefficientMajorant
import GaloisForLFunctions.HTGeometry.PeterssonFormulaLevelOne

/-!
# The Fourier expansion of the Poincaré series

Combining the coset decomposition, the exponential expansion, the Lipschitz sums and the Kloosterman
phases, the Poincaré series of weight `k = k' + 1 ≥ 3` and index `m ≥ 1` has the absolutely
convergent expansion

  `P_m(z) = (1 + (-1)^k) Σ_{n ≥ 0} [δ_{nm} + Σ_{c ≥ 1} Σ_{j ≥ 0} B(c, j) n^{k-1+j} S(m, n; c)] q^n`,

`B(c, j) = (-2πi m/c)^j/j! · c^{-(k+j)} · (-2πi)^{k+j}/(k+j-1)!`, `q = e(z)`.  The four-fold family
is dominated by the product majorant, so the sum may be reordered with `n` outermost, and the
uniqueness of `q`-expansion coefficients identifies the bracket with `a_{P_m}(n)`.
-/

open UpperHalfPlane hiding I
open Complex RHTower.Sieve
open scoped Real MatrixGroups

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Norms of the phases -/

theorem norm_exp_two_pi_I_mul_real (t : ℝ) : ‖Complex.exp (2 * π * I * t)‖ = 1 := by
  rw [show (2 * π * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_exp_phase_top (c : ℕ+) (u : (ZMod c)ˣ) (m : ℕ) :
    ‖Complex.exp (2 * π * I * m * (unitTop c u : ℂ) / c)‖ = 1 := by
  rw [show (2 * π * I * m * (unitTop c u : ℂ) / c)
      = 2 * π * I * ((m * unitTop c u / (c : ℝ) : ℝ) : ℂ) by push_cast; ring]
  exact norm_exp_two_pi_I_mul_real _

theorem norm_exp_phase_val (c : ℕ+) (u : (ZMod c)ˣ) (n : ℕ) :
    ‖Complex.exp (2 * π * I * n * unitVal c u / c)‖ = 1 := by
  rw [show (2 * π * I * n * unitVal c u / c)
      = 2 * π * I * ((n * ((u : ZMod c).val : ℝ) / (c : ℝ) : ℝ) : ℂ) by
        simp only [unitVal]; push_cast; ring]
  exact norm_exp_two_pi_I_mul_real _

theorem norm_exp_two_pi_I_mul_coe (z : ℍ) :
    ‖Complex.exp (2 * π * I * z)‖ = Real.exp (-(2 * π * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-! ## The expansion terms -/

/-- `B(c, j) = (-2πi m/c)^j/j! · c^{-(k'+1+j)} · (-2πi)^{k'+1+j}/(k'+j)!`. -/
def expansionCoeff (k' m : ℕ) (c : ℕ+) (j : ℕ) : ℂ :=
  (-2 * π * I * m / c) ^ j / (j.factorial : ℂ) * ((c : ℂ) ^ (k' + 1 + j))⁻¹ *
    ((-2 * π * I) ^ (k' + 1 + j) / ((k' + j).factorial : ℂ))

/-- The term indexed by `(c, u, j)` and `n`. -/
def expansionTerm (k' m : ℕ) (z : ℍ) (p : CoefIndex) (n : ℕ) : ℂ :=
  Complex.exp (2 * π * I * m * (unitTop p.1 p.2.1 : ℂ) / p.1) * expansionCoeff k' m p.1 p.2.2 *
    ((n : ℂ) ^ (k' + p.2.2) *
      (Complex.exp (2 * π * I * z) ^ n * Complex.exp (2 * π * I * n * unitVal p.1 p.2.1 / p.1)))

theorem exp_shiftedPoint_pow (c : ℕ+) (u : (ZMod c)ˣ) (z : ℍ) (n : ℕ) :
    Complex.exp (2 * π * I * (shiftedPoint c u z : ℂ)) ^ n
      = Complex.exp (2 * π * I * z) ^ n * Complex.exp (2 * π * I * n * unitVal c u / c) := by
  rw [coe_shiftedPoint, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

/-- The coset sum of `(c, u)` is the double series of expansion terms. -/
theorem tsum_cosetTerm_eq_tsum_expansionTerm {k' : ℕ} (hk' : 2 ≤ k') (m : ℕ) (c : ℕ+)
    (u : (ZMod c)ˣ) (z : ℍ) :
    ∑' l : ℤ, cosetTerm ((k' + 1 : ℕ) : ℤ) m c u l z
      = ∑' j : ℕ, ∑' n : ℕ, expansionTerm k' m z ⟨c, (u, j)⟩ n := by
  rw [tsum_cosetTerm_eq c u (by omega) m z, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [tsum_linearShift_zpow c u (by omega : 2 ≤ k' + 1 + j) z]
  simp_rw [exp_shiftedPoint_pow]
  simp only [expansionTerm, expansionCoeff]
  rw [show k' + 1 + j - 1 = k' + j by omega]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

theorem norm_expansionCoeff (k' m : ℕ) (c : ℕ+) (j : ℕ) :
    ‖expansionCoeff k' m c j‖
      = (2 * π * m / (c : ℝ)) ^ j / (j.factorial : ℝ) * (((c : ℕ) : ℝ) ^ (k' + 1 + j))⁻¹ *
          ((2 * π) ^ (k' + 1 + j) / ((k' + j).factorial : ℝ)) := by
  have h1 : ‖(-2 * π * I * m / (c : ℂ))‖ = 2 * π * m / (c : ℝ) := by
    simp [Real.pi_pos.le]
  have h2 : ‖(-2 * π * I : ℂ)‖ = 2 * π := by
    simp [Real.pi_pos.le]
  rw [expansionCoeff, norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow, norm_inv, norm_pow,
    h1, h2, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_natCast]

theorem norm_expansionTerm_le {k' : ℕ} (m : ℕ) (z : ℍ) (p : CoefIndex) (n : ℕ) :
    ‖expansionTerm k' m z p n‖ ≤ coefMajorant k' m z.im p n := by
  obtain ⟨c, u, j⟩ := p
  refine le_trans (le_of_eq ?_) (term_le_coefMajorant z.im_pos m ⟨c, (u, j)⟩ n)
  simp only [expansionTerm, norm_mul, norm_pow, norm_exp_phase_top, norm_exp_phase_val,
    norm_expansionCoeff, Complex.norm_natCast, norm_exp_two_pi_I_mul_coe, one_mul, mul_one,
    ← Real.exp_nat_mul]
  ring_nf

/-- **Absolute convergence** of the four-fold expansion. -/
theorem summable_expansionTerm {k' : ℕ} (hk' : 2 ≤ k') (m : ℕ) (z : ℍ) :
    Summable fun x : CoefIndex × ℕ => expansionTerm k' m z x.1 x.2 :=
  Summable.of_norm_bounded (summable_coefMajorant hk' m z.im_pos) fun x =>
    norm_expansionTerm_le m z x.1 x.2

/-! ## The coefficients -/

/-- The `n`-th Fourier coefficient of `P_m` (weight `k' + 1`):
`(1 + (-1)^k)[δ_{nm} + Σ_c Σ_j B(c,j) n^{k'+j} S(m,n;c)]`. -/
def poincareCoeff (k' m : ℕ) (n : ℕ) : ℂ :=
  (1 + (-1 : ℂ) ^ (k' + 1)) * ((if n = m then 1 else 0) +
    ∑' c : ℕ+, ∑' j : ℕ,
      expansionCoeff k' m c j * (n : ℂ) ^ (k' + j) * kloostermanSum c (m : ZMod c) (n : ZMod c))

/-- For fixed `n`, the sum over `(c, u, j)` collapses the units into Kloosterman sums. -/
theorem tsum_expansionTerm_fixed {k' : ℕ} (hk' : 2 ≤ k') (m : ℕ) (z : ℍ) (n : ℕ) :
    ∑' p : CoefIndex, expansionTerm k' m z p n
      = (∑' c : ℕ+, ∑' j : ℕ,
          expansionCoeff k' m c j * (n : ℂ) ^ (k' + j) * kloostermanSum c (m : ZMod c) (n : ZMod c))
        * Complex.exp (2 * π * I * z) ^ n := by
  have hs : Summable fun p : CoefIndex => expansionTerm k' m z p n :=
    (summable_expansionTerm hk' m z).prod_symm.prod_factor n
  rw [hs.tsum_sigma, ← tsum_mul_right]
  refine tsum_congr fun c => ?_
  have hsc : Summable fun q : (ZMod c)ˣ × ℕ => expansionTerm k' m z ⟨c, q⟩ n := hs.sigma_factor c
  rw [hsc.tsum_prod, tsum_fintype, ← Summable.tsum_finsetSum (fun u _ => hsc.prod_factor u),
    ← tsum_mul_right]
  refine tsum_congr fun j => ?_
  rw [← sum_exp_phase_eq_kloostermanSum c m n, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [expansionTerm]
  ring

/-- **The Fourier expansion of the Poincaré series.** -/
theorem hasSum_poincareCoeff {k' : ℕ} (hk' : 2 ≤ k') (m : ℕ) (z : ℍ) :
    HasSum (fun n : ℕ => poincareCoeff k' m n • Complex.exp (2 * π * I * z) ^ n)
      (poincareSeries ((k' + 1 : ℕ) : ℤ) m z) := by
  have hG := summable_expansionTerm hk' m z
  have hk : 3 ≤ ((k' + 1 : ℕ) : ℤ) := by omega
  have hP := poincareSeries_eq_cosetSum hk m z
  have hlink : ∀ (c : ℕ+) (u : (ZMod c)ˣ), ∑' l : ℤ, cosetTerm ((k' + 1 : ℕ) : ℤ) m c u l z
      = ∑' j : ℕ, ∑' n : ℕ, expansionTerm k' m z ⟨c, (u, j)⟩ n :=
    fun c u => tsum_cosetTerm_eq_tsum_expansionTerm hk' m c u z
  simp_rw [hlink] at hP
  have hG' : Summable (Function.uncurry fun (p : CoefIndex) (n : ℕ) => expansionTerm k' m z p n) :=
    hG
  have hsum1 : ∑' c : ℕ+, ∑' u : (ZMod c)ˣ, ∑' j : ℕ, ∑' n : ℕ, expansionTerm k' m z ⟨c, (u, j)⟩ n
      = ∑' n : ℕ, ∑' p : CoefIndex, expansionTerm k' m z p n := by
    rw [hG'.tsum_comm, hG.prod.tsum_sigma]
    refine tsum_congr fun c => ?_
    rw [(hG.prod.sigma_factor c).tsum_prod]
  rw [hsum1] at hP
  have hn : Summable fun n : ℕ => ∑' p : CoefIndex, expansionTerm k' m z p n := hG.prod_symm.prod
  have h1 := hn.hasSum
  have h0 : HasSum (fun n : ℕ => if n = m then Complex.exp (2 * π * I * z) ^ m else 0)
      (Complex.exp (2 * π * I * z) ^ m) := hasSum_ite_eq m _
  have hsum := (h0.add h1).mul_left (1 + (-1 : ℂ) ^ (k' + 1))
  have hexp : expSeed m z = Complex.exp (2 * π * I * z) ^ m := by
    rw [expSeed, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hε : ((-1 : ℂ) ^ ((k' + 1 : ℕ) : ℤ)) = (-1) ^ (k' + 1) := zpow_natCast _ _
  have hf : (fun n : ℕ => poincareCoeff k' m n • Complex.exp (2 * π * I * z) ^ n)
      = fun n : ℕ => (1 + (-1 : ℂ) ^ (k' + 1)) *
          ((if n = m then Complex.exp (2 * π * I * z) ^ m else 0) +
            ∑' p : CoefIndex, expansionTerm k' m z p n) := by
    funext n
    rw [smul_eq_mul, poincareCoeff, tsum_expansionTerm_fixed hk' m z n]
    by_cases h : n = m
    · subst h
      simp only [if_true]
      ring
    · simp only [if_neg h]
      ring
  have hv : poincareSeries ((k' + 1 : ℕ) : ℤ) m z
      = (1 + (-1 : ℂ) ^ (k' + 1)) * (Complex.exp (2 * π * I * z) ^ m +
          ∑' n : ℕ, ∑' p : CoefIndex, expansionTerm k' m z p n) := by
    rw [hP, hexp, hε]
    ring
  rw [hf, hv]
  exact hsum

/-- **The Fourier coefficients of the Poincaré cusp form.** -/
theorem cuspCoeff_poincareSeriesCF_eq_poincareCoeff {k' : ℕ} (hk' : 2 ≤ k') {m : ℕ}
    (hm : 1 ≤ m) (n : ℕ) :
    cuspCoeff n (poincareSeriesCF (k := ((k' + 1 : ℕ) : ℤ)) (by omega) hm) = poincareCoeff k' m n := by
  unfold cuspCoeff
  symm
  refine ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL2Z
    (f := poincareSeriesCF (k := ((k' + 1 : ℕ) : ℤ)) (by omega) hm) (fun τ => ?_) n
  have := hasSum_poincareCoeff hk' m τ
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  exact this

end

end GaloisForLFunctions.HTGeometry
