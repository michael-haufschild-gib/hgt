import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty

/-!
# Holomorphic Poincaré series of level one

For `k ≥ 3` and `m ≥ 0` the Poincaré series of weight `k` and index `m` is

`P_m(z) = Σ_{(c,d) coprime} (cz + d)^{-k} · e(m · M_{c,d} z)`,

where `M_{c,d} ∈ SL(2,ℤ)` is any matrix with bottom row `(c, d)` and `e(w) = exp(2πiw)`.  The
exponential factor depends only on the bottom row: two determinant-one matrices with the same
bottom row differ by a left translation, so their Möbius images differ by an integer.  The factor
has modulus at most one on the upper half-plane, so every convergence statement for the Eisenstein
summand `(cz+d)^{-k}` transfers verbatim: absolute convergence, locally uniform convergence, and the
weight-`k` transformation law `P_m(γz) = (cz+d)^k P_m(z)` obtained by reindexing the coprime pairs
by the right action of `γ`.

The index set and the summand bounds are those of mathlib's Eisenstein series
(`EisensteinSeries.gammaSet 1 1 0`, `eisSummand`, `summand_bound_of_mem_verticalStrip`).
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularForm Complex Matrix
open scoped MatrixGroups Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## A determinant-one matrix with prescribed coprime bottom row -/

/-- The matrix `!![gcdB, -gcdA; c, d]` built from a Bézout relation `c·gcdA + d·gcdB = 1`. -/
def bottomRowMatrix (c d : ℤ) (h : c.gcd d = 1) : SL(2, ℤ) :=
  ⟨!![c.gcdB d, -(c.gcdA d); c, d], by
    rw [Matrix.det_fin_two_of]
    have hbez := Int.gcd_eq_gcd_ab c d
    rw [h] at hbez
    push_cast at hbez
    linear_combination hbez.symm⟩

@[simp] theorem bottomRowMatrix_apply_one_zero (c d : ℤ) (h : c.gcd d = 1) :
    bottomRowMatrix c d h 1 0 = c := rfl

@[simp] theorem bottomRowMatrix_apply_one_one (c d : ℤ) (h : c.gcd d = 1) :
    bottomRowMatrix c d h 1 1 = d := rfl

/-- Two determinant-one matrices with the same bottom row have top rows differing by an integer
multiple of the bottom row. -/
theorem exists_int_top_row_of_bottomRow_eq (A B : SL(2, ℤ)) (h0 : A 1 0 = B 1 0)
    (h1 : A 1 1 = B 1 1) :
    ∃ n : ℤ, A 0 0 = B 0 0 + n * A 1 0 ∧ A 0 1 = B 0 1 + n * A 1 1 := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.det_coe
    rwa [Matrix.det_fin_two] at this
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    have := B.det_coe
    rwa [Matrix.det_fin_two] at this
  rw [← h0, ← h1] at hB
  rcases eq_or_ne (A 1 0) 0 with hc0 | hc0
  · -- `c = 0`: then `d = ±1`, the top-left entries agree, and `n = (b − b') d`
    rw [hc0] at hA hB
    simp only [mul_zero, sub_zero] at hA hB
    have hdA : A 1 1 * A 0 0 = 1 := by rw [mul_comm]; exact hA
    have hd1 : A 1 1 = 1 ∨ A 1 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hdA
    have hdd : A 1 1 * A 1 1 = 1 := by
      rcases hd1 with h | h <;> rw [h] <;> norm_num
    have haa : A 0 0 = B 0 0 := by
      rcases hd1 with h | h <;> rw [h] at hA hB <;> linarith
    refine ⟨(A 0 1 - B 0 1) * A 1 1, ?_, ?_⟩
    · rw [hc0, mul_zero, add_zero, haa]
    · linear_combination (-(A 0 1 - B 0 1)) * hdd
  · -- `c ≠ 0`: `(a − a') d = (b − b') c`, and `c` is coprime to `d`
    have hcop : IsCoprime (A 1 0) (A 1 1) := ⟨-(A 0 1), A 0 0, by linear_combination hA⟩
    have hkey : (A 0 0 - B 0 0) * A 1 1 = (A 0 1 - B 0 1) * A 1 0 := by
      linear_combination hA - hB
    have hdvd : A 1 0 ∣ (A 0 0 - B 0 0) * A 1 1 := ⟨A 0 1 - B 0 1, by rw [hkey]; ring⟩
    obtain ⟨n, hn⟩ := hcop.dvd_of_dvd_mul_right hdvd
    refine ⟨n, by linear_combination hn, ?_⟩
    have h2 : (A 0 1 - B 0 1) * A 1 0 = n * A 1 1 * A 1 0 := by
      rw [← hkey, hn]
      ring
    have h3 : A 0 1 - B 0 1 = n * A 1 1 := mul_right_cancel₀ hc0 h2
    linear_combination h3

/-- Möbius images under matrices with the same bottom row differ by an integer. -/
theorem coe_smul_eq_coe_smul_add_int_of_bottomRow_eq (A B : SL(2, ℤ)) (h0 : A 1 0 = B 1 0)
    (h1 : A 1 1 = B 1 1) (z : ℍ) :
    ∃ n : ℤ, ((A • z : ℍ) : ℂ) = ((B • z : ℍ) : ℂ) + n := by
  obtain ⟨n, ha, hb⟩ := exists_int_top_row_of_bottomRow_eq A B h0 h1
  refine ⟨n, ?_⟩
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, ← h0, ← h1]
  have hden : ((A 1 0 : ℤ) : ℂ) * (z : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    have hne : (fun i : Fin 2 => ((A 1 i : ℤ) : ℝ)) ≠ 0 := by
      intro h
      have h0' : A 1 0 = 0 := by
        have := congrFun h 0
        simpa using this
      have h1' : A 1 1 = 0 := by
        have := congrFun h 1
        simpa using this
      have := A.det_coe
      rw [Matrix.det_fin_two, h0', h1'] at this
      simp at this
    simpa using UpperHalfPlane.linear_ne_zero (cd := fun i : Fin 2 => ((A 1 i : ℤ) : ℝ)) z hne
  rw [ha, hb]
  push_cast
  field_simp
  ring

/-- The exponential factor `e(m·Mz)` depends only on the bottom row of `M`. -/
theorem exp_smul_eq_of_bottomRow_eq (m : ℕ) (A B : SL(2, ℤ)) (h0 : A 1 0 = B 1 0)
    (h1 : A 1 1 = B 1 1) (z : ℍ) :
    Complex.exp (2 * π * I * m * ((A • z : ℍ) : ℂ))
      = Complex.exp (2 * π * I * m * ((B • z : ℍ) : ℂ)) := by
  obtain ⟨n, hn⟩ := coe_smul_eq_coe_smul_add_int_of_bottomRow_eq A B h0 h1 z
  rw [hn, mul_add, Complex.exp_add]
  have hone : Complex.exp (2 * π * I * m * n) = 1 := by
    rw [show (2 * π * I * m * n : ℂ) = ((m * n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hone, mul_one]

/-! ## The Poincaré summand and series -/

/-- A coprime pair as a determinant-one matrix with that bottom row. -/
def gammaSetMatrix (v : gammaSet 1 1 0) : SL(2, ℤ) :=
  bottomRowMatrix (v.1 0) (v.1 1) ((gammaSet_one_mem_iff 1 v.1).mp v.2)

@[simp] theorem gammaSetMatrix_apply_one_zero (v : gammaSet 1 1 0) :
    gammaSetMatrix v 1 0 = v.1 0 := rfl

@[simp] theorem gammaSetMatrix_apply_one_one (v : gammaSet 1 1 0) :
    gammaSetMatrix v 1 1 = v.1 1 := rfl

/-- The Poincaré summand `(cz+d)^{-k} e(m · M_{c,d} z)`. -/
def poincareSummand (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0) (z : ℍ) : ℂ :=
  eisSummand k v.1 z * Complex.exp (2 * π * I * m * ((gammaSetMatrix v • z : ℍ) : ℂ))

/-- The Poincaré series of weight `k` and index `m`, summed over coprime pairs. -/
def poincareSeries (k : ℤ) (m : ℕ) (z : ℍ) : ℂ :=
  ∑' v : gammaSet 1 1 0, poincareSummand k m v z

/-- `‖e(m w)‖ ≤ 1` on the upper half-plane. -/
theorem norm_exp_two_pi_I_mul_le_one (m : ℕ) (w : ℍ) :
    ‖Complex.exp (2 * π * I * m * (w : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * π * I * m * (w : ℂ)).re = -(2 * π * m * w.im) := by
    have : (2 * π * I * m * (w : ℂ)) = ((2 * π * m : ℝ) : ℂ) * (I * (w : ℂ)) := by
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
    ring
  rw [hre]
  have : 0 ≤ 2 * π * m * w.im := by
    have := w.im_pos
    positivity
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem norm_poincareSummand_le (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0) (z : ℍ) :
    ‖poincareSummand k m v z‖ ≤ ‖eisSummand k v.1 z‖ := by
  unfold poincareSummand
  rw [norm_mul]
  calc ‖eisSummand k v.1 z‖ * ‖Complex.exp (2 * π * I * m * ((gammaSetMatrix v • z : ℍ) : ℂ))‖
      ≤ ‖eisSummand k v.1 z‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_exp_two_pi_I_mul_le_one m _) (norm_nonneg _)
    _ = ‖eisSummand k v.1 z‖ := mul_one _

/-- Absolute convergence for `k ≥ 3`. -/
theorem summable_norm_poincareSummand {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    Summable fun v : gammaSet 1 1 0 => ‖poincareSummand k m v z‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => norm_poincareSummand_le k m v z)
    ((summable_norm_eisSummand hk z).subtype _)

theorem summable_poincareSummand {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    Summable fun v : gammaSet 1 1 0 => poincareSummand k m v z :=
  (summable_norm_poincareSummand hk m z).of_norm

/-- The Poincaré series converges locally uniformly on `ℍ` for `k ≥ 3`. -/
theorem poincareSeries_tendstoLocallyUniformly {k : ℤ} (hk : 3 ≤ k) (m : ℕ) :
    TendstoLocallyUniformly
      (fun (s : Finset (gammaSet 1 1 0)) ↦ (∑ x ∈ s, poincareSummand k m x ·))
      (poincareSeries k m ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have p_sum : Summable fun x : gammaSet 1 1 0 ↦ ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (gammaSet 1 1 0)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, poincareSeries]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun p z hz ↦ ?_)).mono HABK
  refine (norm_poincareSummand_le k m p z).trans ?_
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p.1 hB hz

/-! ## The transformation law -/

/-- The right action of `γ` on coprime pairs, as a self-equivalence of the level-one index set. -/
def gammaSetSelfEquiv (γ : SL(2, ℤ)) : gammaSet 1 1 0 ≃ gammaSet 1 1 0 :=
  (gammaSetEquiv (0 : Fin 2 → ZMod 1) γ).trans
    (Equiv.setCongr (gammaSet_one_const 1 ((0 : Fin 2 → ZMod 1) ᵥ* γ) 0))

theorem gammaSetSelfEquiv_apply_val (γ : SL(2, ℤ)) (v : gammaSet 1 1 0) :
    (gammaSetSelfEquiv γ v).1 = v.1 ᵥ* γ := rfl

/-- The bottom row of `M_v · γ` is `v ᵥ* γ`. -/
theorem gammaSetMatrix_mul_apply_one (v : gammaSet 1 1 0) (γ : SL(2, ℤ)) (j : Fin 2) :
    (gammaSetMatrix v * γ) 1 j = (v.1 ᵥ* γ) j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp

/-- One summand transforms with the automorphy factor and the reindexed pair. -/
theorem poincareSummand_SL2_apply (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0) (γ : SL(2, ℤ)) (z : ℍ) :
    poincareSummand k m v (γ • z)
      = denom γ z ^ k * poincareSummand k m (gammaSetSelfEquiv γ v) z := by
  unfold poincareSummand
  rw [eisSummand_SL2_apply, gammaSetSelfEquiv_apply_val, mul_assoc]
  congr 2
  rw [← mul_smul]
  refine exp_smul_eq_of_bottomRow_eq m _ _ ?_ ?_ z
  · rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_zero, gammaSetSelfEquiv_apply_val]
  · rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_one, gammaSetSelfEquiv_apply_val]

/-- **Weight-`k` transformation law** of the Poincaré series. -/
theorem poincareSeries_slash_apply (k : ℤ) (m : ℕ) (γ : SL(2, ℤ)) :
    poincareSeries k m ∣[k] γ = poincareSeries k m := by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    poincareSeries, poincareSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (gammaSetSelfEquiv γ).tsum_eq (poincareSummand k m · z)

end

end GaloisForLFunctions.HTGeometry
