import GaloisForLFunctions.RHTower.WeilLogShiftFiniteReconstruction
import GaloisForLFunctions.RHTower.WeilAbsoluteConvergenceRigidity

/-!
# Uniform finite Gram certificates for finite arithmetic packets

Existing positive-definite rigidity, combined with finite-dimensional
compactness, yields finitely many actual Gram tests with a uniform margin.
Approximate nonnegativity bounds the coefficient norm.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The finite potential already represented by the native arithmetic series. -/
def finiteWeilPotential (s : Finset ℕ) (c : s → ℝ) (y : ℝ) : ℝ :=
  ∑ i : s, c i * pairedLogKernel y ((i : ℕ) + 2)

theorem finiteWeilPacket_apply_tail (s : Finset ℕ) (c : s → ℝ) (i : s) :
    finiteWeilPacket s c ((i : ℕ) + 2) = c i := by
  classical
  simp only [finiteWeilPacket, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Finsupp.single_apply]
    apply if_neg
    intro h
    exact hji (Subtype.ext (Nat.add_right_cancel h))
  · simp

theorem nullPotential_finiteWeilPacket (s : Finset ℕ) (c : s → ℝ) (y : ℝ) :
    WeilRegular.nullPotential (finiteWeilPacket s c) y = finiteWeilPotential s c y := by
  have h : HasSum (fun n : ℕ => finiteWeilPacket s c n * pairedLogKernel y n)
      ((finiteWeilPacket s c).sum (fun n a => a * pairedLogKernel y n)) :=
    hasSum_sum_of_ne_finset_zero (s := (finiteWeilPacket s c).support)
      (fun n hn => by rw [Finsupp.notMem_support_iff.mp hn, zero_mul])
  exact h.tsum_eq.trans (finiteWeilPacket_synthesis s c y)

/-- All regularity assumptions of the existing rigidity theorem are
discharged for the finite packet. -/
theorem finiteWeilPotential_positiveDefinite_iff (s : Finset ℕ) (c : s → ℝ) :
    PositiveDefiniteOnReal (fun y => ((-finiteWeilPotential s c y : ℝ) : ℂ)) ↔ c = 0 := by
  classical
  constructor
  · intro hPD
    let v := finiteWeilPacket s c
    let A := ∑ n ∈ v.support, |v n|
    have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hbound (n : ℕ) : |v n| ≤ A := by
      by_cases hn : n ∈ v.support
      · exact Finset.single_le_sum (f := fun k => |v k|)
          (fun k _ => abs_nonneg (v k)) hn
      · rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
        exact hA
    have hlog (n : ℕ) : |v n| ≤ 2 * Real.log n + A := by
      have := Real.log_natCast_nonneg n
      linarith [hbound n]
    have hsum : Summable (fun n : ℕ => |v n| * (Real.sqrt n)⁻¹) :=
      (hasSum_sum_of_ne_finset_zero (s := v.support)
        (fun n hn => by rw [Finsupp.notMem_support_iff.mp hn, abs_zero, zero_mul])).summable
    have hzero := WeilAbscissa.eq_zero_of_positiveDefinite_neg_nullPotential_of_sqrt_summable
      (finiteWeilPacket_head s c 0 (by omega))
      (finiteWeilPacket_head s c 1 (by omega)) hA hlog hsum
      (by simpa only [v, nullPotential_finiteWeilPacket] using hPD)
    funext i
    have h := congrFun hzero ((i : ℕ) + 2)
    simpa only [v, finiteWeilPacket_apply_tail, Pi.zero_apply] using h
  · rintro rfl
    intro N x u
    refine ⟨0, le_rfl, ?_⟩
    simp [finiteWeilPotential]

-- Real-even Gram bridge, using the real/imaginary splitting already used
-- by WeilWorkExposingRayPolarKernel's private helper.
private theorem positiveDefinite_of_real_even {k : ℝ → ℝ}
    (heven : ∀ y, k (-y) = k y)
    (hpos : ∀ (N : ℕ) (x c : Fin N → ℝ),
      0 ≤ ∑ i, ∑ j, (c i * c j) * k (x j - x i)) :
    PositiveDefiniteOnReal (fun y => (k y : ℂ)) := by
  intro N x c
  let R : ℝ := (∑ i, ∑ j, ((c i).re * (c j).re) * k (x j - x i)) +
    ∑ i, ∑ j, ((c i).im * (c j).im) * k (x j - x i)
  refine ⟨R, add_nonneg (hpos N x (fun i => (c i).re))
    (hpos N x (fun i => (c i).im)), ?_⟩
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    dsimp [R]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have hswap : (∑ i, ∑ j, (c i).re * k (x j - x i) * (c j).im) =
        ∑ i, ∑ j, (c i).im * k (x j - x i) * (c j).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hk : k (x i - x j) = k (x j - x i) := by
        rw [show x i - x j = -(x j - x i) by ring, heven]
      rw [hk]
      ring
    calc
      _ = (∑ i, ∑ j, (c i).re * k (x j - x i) * (c j).im) -
          ∑ i, ∑ j, (c i).im * k (x j - x i) * (c j).re := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hswap, sub_self]

/-- An actual real Gram test together with a nonnegative normalization. -/
abbrev FiniteWeilGramTest := Σ N : ℕ, (Fin N → ℝ) × (Fin N → ℝ) × NNReal

/-- The normalized Gram energy of the negative finite potential, linear
in arithmetic coefficients. -/
def finiteWeilGramForm (s : Finset ℕ) : FiniteWeilGramTest → (s → ℝ) →ₗ[ℝ] ℝ
  | ⟨N, x, u, a⟩ => -(a : ℝ) • ∑ i : Fin N, ∑ j : Fin N,
      (u i * u j) • ∑ k : s,
        pairedLogKernel (x j - x i) ((k : ℕ) + 2) • LinearMap.proj k

theorem finiteWeilGramForm_apply (s : Finset ℕ) (N : ℕ)
    (x u : Fin N → ℝ) (a : NNReal) (c : s → ℝ) :
    finiteWeilGramForm s ⟨N, x, u, a⟩ c = -(a : ℝ) *
      ∑ i, ∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i) := by
  simp [finiteWeilGramForm, finiteWeilPotential, mul_comm]

/-- These are Gram tests of the actual arithmetic deviation potential.
The imported finite-packet `HasSum` theorem justifies its series value. -/
theorem finiteWeilGramForm_native (s : Finset ℕ) (N : ℕ)
    (x u : Fin N → ℝ) (a : NNReal) (c : s → ℝ) :
    finiteWeilGramForm s ⟨N, x, u, a⟩ c = -(a : ℝ) *
      ∑ i, ∑ j, (u i * u j) * WeilExcess.deviationPotential
        (weilCoefficientLift (finiteWeilPacket s c)) (x j - x i) := by
  have hpotential (y : ℝ) : WeilExcess.deviationPotential
      (weilCoefficientLift (finiteWeilPacket s c)) y = finiteWeilPotential s c y :=
    (hasSum_finiteWeilPacket_deviation s c y).tsum_eq
  simpa only [hpotential] using finiteWeilGramForm_apply s N x u a c

private theorem exists_normalized_finiteWeilGram (s : Finset ℕ) (c : s → ℝ)
    (hc : c ≠ 0) : ∃ w : FiniteWeilGramTest, finiteWeilGramForm s w c = -2 := by
  classical
  have hex : ∃ (N : ℕ) (x u : Fin N → ℝ),
      0 < ∑ i, ∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i) := by
    by_contra h
    push Not at h
    apply hc
    apply (finiteWeilPotential_positiveDefinite_iff s c).mp
    apply positiveDefinite_of_real_even
    · intro y
      simp [finiteWeilPotential, pairedLogKernel_neg]
    · intro N x u
      simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonneg] using h N x u
  obtain ⟨N, x, u, hS⟩ := hex
  let S := ∑ i, ∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i)
  let a : NNReal := ⟨2 / S, (div_pos (by norm_num) hS).le⟩
  refine ⟨⟨N, x, u, a⟩, ?_⟩
  rw [finiteWeilGramForm_apply]
  change -(2 / S) * S = -2
  rw [neg_mul, div_mul_cancel₀ _ hS.ne']

/-- Fixed finitely many actual Gram tests detect every nonzero coefficient
packet with a norm margin. No positivity or regularity premise is assumed. -/
theorem exists_finiteWeilGram_norm_certificate (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, ∀ c : s → ℝ, c ≠ 0 →
      ∃ w ∈ tests, finiteWeilGramForm s w c < -‖c‖ := by
  classical
  let U (w : FiniteWeilGramTest) : Set (s → ℝ) :=
    {c | finiteWeilGramForm s w c < -1}
  have hU (w : FiniteWeilGramTest) : IsOpen (U w) :=
    isOpen_lt (finiteWeilGramForm s w).continuous_of_finiteDimensional continuous_const
  have hcover : Metric.sphere (0 : s → ℝ) 1 ⊆ ⋃ w, U w := by
    intro c hc
    have hn : ‖c‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hc
    have hne : c ≠ 0 := by
      intro h
      simp only [h, norm_zero, zero_ne_one] at hn
    obtain ⟨w, hw⟩ := exists_normalized_finiteWeilGram s c hne
    exact Set.mem_iUnion.mpr ⟨w, by change finiteWeilGramForm s w c < -1; linarith⟩
  obtain ⟨tests, htests⟩ :=
    (isCompact_sphere (0 : s → ℝ) 1).elim_finite_subcover U hU hcover
  refine ⟨tests, ?_⟩
  intro c hc
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hunit : (‖c‖⁻¹ : ℝ) • c ∈ Metric.sphere (0 : s → ℝ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (htests hunit)
  obtain ⟨hmem, hvalue⟩ := Set.mem_iUnion.mp hw
  refine ⟨w, hmem, ?_⟩
  change finiteWeilGramForm s w ((‖c‖⁻¹ : ℝ) • c) < -1 at hvalue
  rw [map_smul, smul_eq_mul] at hvalue
  have h := mul_lt_mul_of_pos_left hvalue hn
  simpa only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_neg, mul_one] using h

/-- Approximate nonnegativity of finitely many normalized Gram tests bounds
the coefficient error; exact nonnegativity characterizes the zero packet. -/
theorem exists_finiteWeilGram_stability_certificate (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest,
      (∀ (c : s → ℝ) (ε : ℝ), 0 ≤ ε →
        (∀ w ∈ tests, -ε ≤ finiteWeilGramForm s w c) → ‖c‖ ≤ ε) ∧
      ∀ c : s → ℝ, (∀ w ∈ tests, 0 ≤ finiteWeilGramForm s w c) ↔ c = 0 := by
  obtain ⟨tests, htests⟩ := exists_finiteWeilGram_norm_certificate s
  have hbound (c : s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (hc : ∀ w ∈ tests, -ε ≤ finiteWeilGramForm s w c) : ‖c‖ ≤ ε := by
    by_cases hzero : c = 0
    · simpa only [hzero, norm_zero] using hε
    · obtain ⟨w, hw, hvalue⟩ := htests c hzero
      have := hc w hw
      linarith
  refine ⟨tests, hbound, ?_⟩
  intro c
  constructor
  · intro hc
    exact norm_eq_zero.mp (le_antisymm (hbound c 0 le_rfl (by simpa using hc)) (norm_nonneg c))
  · rintro rfl
    intro w _
    simp only [map_zero, le_refl]

end RHTower
