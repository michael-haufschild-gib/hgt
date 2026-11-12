import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EverySparseConfigurationIsRealized
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ACountBelowTheDeletionExponentIsARealZero

/-!
# Twins continue past the line

The factorization `(s − 1) ζ_B(s) = (s − 1) ζ(s) · C · L(s) · e^{H(s)}` of the greedy edit of a
target of size `A k^{−η}` was stated with `H` holomorphic on `Re s > 1/2`.  Two half-planes
decide how far it holds: the discrepancy of the edit is `O(n^c)` for every `c > 17/30 − η`, and
the edited primes are summable at every `θ > 1 − η`, so the prime-power remainder is holomorphic
on `Re s > (1 − η)/2`.

**Theorem** (`isFactorTwinOn_gedit`).  For `0 < η < 1` and
`max(17/30 − η, (1 − η)/2) < c ≤ 1` the edit is a twin with the factor `L` on `Re s > c`
(`IsFactorTwinOn`), if `L′/L = −Σ m(k) k^{−s} − Φ₀` with `Φ₀` holomorphic on `Re s > c`.

* **The pair twin** (`isFactorTwinOn_edit`).  `η = 1 − Re ρ`: the factorization with
  `L = (s − ρ)(s − ρ̄)` holds on `Re s > max(Re ρ − 13/30, Re ρ/2)`, a half-plane that contains
  the critical line for `Re ρ < 14/15`.  So `ζ_B` is holomorphic there apart from the pole at
  `1`, and its zeros are those of `ζ` and `ρ, ρ̄`.
* **No reflection** (`exists_continuation_not_symmetric`).  For `1/2 < Re ρ < 2/3` the reflected
  point `1 − ρ̄` lies in the half-plane, and `ζ_B(1 − ρ̄) ≠ 0` unless `ζ(1 − ρ̄) = 0`: the zeros of
  the twin are not symmetric about the line.
* **Every finite layer below `1`** (`exists_isEdit_layerTwinOn`).  For `Re ρ_j ≤ b < 1` the edit
  of the layer is a twin on `Re s > max(b − 13/30, b/2)`; this half-plane is right of the line
  only for `b > 14/15`, and it always contains `Re s ≥ 17/30`.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

/-- `B` is a **twin of `ζ` with the factor `L` on the half-plane `Re s > c`**. -/
def IsFactorTwinOn (c : ℝ) (B : BeurlingSystem) (L : ℂ → ℂ) : Prop :=
  ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | c < s.re} ∧
    ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * L s * Complex.exp (H s))

/-- The mass of a target of size `A k^{−η}` is `O(n^{1−η})`. -/
theorem sum_abs_le_of_abs_le {m : ℕ → ℝ} {A η : ℝ} (hA : 0 ≤ A) (hη1 : η < 1)
    (hm : ∀ k : ℕ, 1 ≤ k → |m k| ≤ A * (k : ℝ) ^ (-η)) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |m k| ≤ A / (1 - η) * (n : ℝ) ^ (1 - η) := by
  have hθ : 0 < 1 - η := by linarith
  have hI : Ioc 0 n = Icc 1 n := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  calc ∑ k ∈ Ioc 0 n, |m k| ≤ ∑ k ∈ Icc 1 n, A * (k : ℝ) ^ ((1 - η) - 1) := by
        rw [hI]
        refine Finset.sum_le_sum fun k hk => ?_
        rw [show (1 - η) - 1 = -η by ring]
        exact hm k (Finset.mem_Icc.mp hk).1
    _ = A * ∑ k ∈ Icc 1 n, (k : ℝ) ^ ((1 - η) - 1) := by rw [Finset.mul_sum]
    _ ≤ A * ((n : ℝ) ^ (1 - η) / (1 - η)) :=
        mul_le_mul_of_nonneg_left (DeletionData.sum_rpow_le hθ (by linarith) n) hA
    _ = A / (1 - η) * (n : ℝ) ^ (1 - η) := by ring

/-- **The greedy edit of a target is a twin on `Re s > max(17/30 − η, (1 − η)/2)`.** -/
theorem isFactorTwinOn_gedit {m : ℕ → ℝ} {A η c : ℝ} (hA : 0 ≤ A) (hη0 : 0 < η)
    (hη1 : η < 1) (hc1 : 17 / 30 - η < c) (hc2 : (1 - η) / 2 < c) (hc3 : c ≤ 1)
    (hm0 : m 0 = 0) (hm : ∀ k : ℕ, 1 ≤ k → |m k| ≤ A * (k : ℝ) ^ (-η))
    {L Φ₀ : ℂ → ℂ} (hΦ₀ : DifferentiableOn ℂ Φ₀ {s : ℂ | c < s.re})
    (hL : ∀ s : ℂ, 1 < s.re → L s ≠ 0 ∧ DifferentiableAt ℂ L s ∧
      logDeriv L s = -LSeries (fun k => (m k : ℂ)) s - Φ₀ s) :
    IsFactorTwinOn c (editSystem (gedit m)) L := by
  have hc0 : 0 < c := by linarith
  -- an exponent of the prime window with `α − η ≤ c`
  obtain ⟨α, hα0, hα1, hαc⟩ : ∃ α : ℝ, 17 / 30 < α ∧ α < 1 ∧ α - η ≤ c := by
    by_cases h : (17 / 30 + (c + η)) / 2 < 1
    · exact ⟨(17 / 30 + (c + η)) / 2, by linarith, h, by linarith⟩
    · exact ⟨9 / 10, by norm_num, by norm_num, by linarith [not_lt.mp h]⟩
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_le_rpow_of_abs_le (m := m) (A := A) (η := η)
    (c := c) hA hη0 hη1.le hm hα1 hc0 hαc hwin
  have hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (m k : ℂ)) s := by
    intro s hs
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1 - η) (by linarith)
      ⟨A, fun n hn => ?_⟩
    show ‖((m n : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, show 1 - η - 1 = -η by ring]
    exact hm n (Nat.one_le_iff_ne_zero.mpr hn)
  obtain ⟨C, K, hC, hK, hfac⟩ := exists_exp_geditSeries_eq (m := m) hm0 hK₀ hc0 hc3 hdisc
    hsumm (L := L) hΦ₀ hL
  have he := isEdit_gedit m
  -- the edited primes are summable at `2c`: the prime-power remainder is holomorphic on `Re s > c`
  have hthin : Summable fun k : ℕ => |(gedit m k : ℝ)| * (k : ℝ) ^ (-(2 * c)) :=
    summable_abs_gedit_rpow (θ := 1 - η) (by linarith) (K := A / (1 - η))
      (div_nonneg hA (by linarith)) (fun n _ => sum_abs_le_of_abs_le hA hη1 hm n) (by linarith)
  have hQ : DifferentiableOn ℂ (editRem (gedit m)) {s : ℂ | c < s.re} := by
    have h := BalanceLaw.differentiableOn_editRem_of_summable (θ := 2 * c) (by linarith) hthin
    rwa [show 2 * c / 2 = c by ring] at h
  refine ⟨C, fun s => K s + editRem (gedit m) s, hC, hK.add hQ, fun s hs => ?_⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hEK : Complex.exp (LSeries (fun k => (gedit m k : ℂ)) s + editRem (gedit m) s) =
      C * L s * Complex.exp (K s + editRem (gedit m) s) := by
    rw [Complex.exp_add, hfac s hs, Complex.exp_add]
    ring
  rw [editSystem_zetaSeriesC he hs, hEK, zetaResidueUnit_of_ne hs1]
  ring

/-- On `Re s > c` the continuation of `(s − 1) ζ_B(s)` of a twin vanishes, away from `1` and the
zeros of `ζ`, exactly at the zeros of the factor. -/
theorem IsFactorTwinOn.exists_continuation {c : ℝ} {B : BeurlingSystem} {L : ℂ → ℂ}
    (h : IsFactorTwinOn c B L) (hL : DifferentiableOn ℂ L {s : ℂ | c < s.re}) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧
      ∀ z : ℂ, c < z.re → z ≠ 1 → riemannZeta z ≠ 0 → (G z = 0 ↔ L z = 0) := by
  obtain ⟨C, H, hC, hH, hfac⟩ := h
  refine ⟨fun s => zetaResidueUnit s * (C * L s * Complex.exp (H s)),
    differentiable_zetaResidueUnit.differentiableOn.mul
      (((differentiableOn_const C).mul hL).mul hH.cexp),
    fun s hs => (hfac s hs).symm, fun z _ hz1 hzζ => ?_⟩
  have hzu : zetaResidueUnit z ≠ 0 := by
    rw [zetaResidueUnit_of_ne hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ
  simp only [mul_eq_zero, hzu, hC, Complex.exp_ne_zero, false_or, or_false]

/-! ## The pair twin -/

/-- **The pair twin continues past the line**: the factorization with the pair `ρ, ρ̄` holds on
`Re s > max(Re ρ − 13/30, Re ρ/2)`. -/
theorem isFactorTwinOn_edit {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ.re < 1) {c : ℝ}
    (hc1 : ρ.re - 13 / 30 < c) (hc2 : ρ.re / 2 < c) (hc3 : c ≤ 1) :
    IsFactorTwinOn c (editSystem (edit ρ)) (fun s => (s - ρ) * (s - (starRingEnd ℂ) ρ)) := by
  refine isFactorTwinOn_gedit (A := 2) (η := 1 - ρ.re) (by norm_num) (by linarith)
    (by linarith) (by linarith) (by linarith) hc3 (target_zero hρ1)
    (fun k hk => by
      have h := abs_target_le ρ hk
      rwa [show ρ.re - 1 = -(1 - ρ.re) by ring] at h)
    (Φ₀ := fun s => PrimeEdits.zetaRegular (s - (ρ - 1)) +
      PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) ρ - 1)))
    ?_ (fun s hs => logDeriv_pair_eq hρ1 hs)
  exact ((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
    (PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _))).differentiableOn

/-- **The zeros of the pair twin are not symmetric about the line.**  For `1/2 < Re ρ < 2/3`,
`(s − 1) ζ_B(s)` continues to a half-plane `Re s > c` with `c < 1 − Re ρ`; the continuation
vanishes at `ρ` and, if `ζ(1 − ρ̄) ≠ 0`, not at the reflected point `1 − ρ̄`. -/
theorem exists_continuation_not_symmetric {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ2 : ρ.re < 2 / 3)
    (hζ : riemannZeta (1 - (starRingEnd ℂ) ρ) ≠ 0) :
    ∃ (c : ℝ) (G : ℂ → ℂ), c < 1 - ρ.re ∧ DifferentiableOn ℂ G {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem (edit ρ)).zetaSeriesC s) ∧
      G ρ = 0 ∧ G (1 - (starRingEnd ℂ) ρ) ≠ 0 := by
  obtain ⟨C, H, hC, hH, hfac⟩ := isFactorTwinOn_edit (ρ := ρ) (c := 1 / 2 - ρ.re / 4)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨1 / 2 - ρ.re / 4, fun s => zetaResidueUnit s *
    (C * ((s - ρ) * (s - (starRingEnd ℂ) ρ)) * Complex.exp (H s)), by linarith, ?_,
    fun s hs => (hfac s hs).symm, ?_, ?_⟩
  · refine differentiable_zetaResidueUnit.differentiableOn.mul
      (((differentiableOn_const C).mul ?_).mul hH.cexp)
    exact ((differentiable_id.sub_const ρ).mul
      (differentiable_id.sub_const ((starRingEnd ℂ) ρ))).differentiableOn
  · show zetaResidueUnit ρ * (C * ((ρ - ρ) * (ρ - (starRingEnd ℂ) ρ)) * Complex.exp (H ρ)) = 0
    rw [sub_self, zero_mul, mul_zero, zero_mul, mul_zero]
  · have hz1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h'
      linarith
    have h1 : (1 : ℂ) - (starRingEnd ℂ) ρ - ρ ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at h'
      linarith
    have h2 : (1 : ℂ) - (starRingEnd ℂ) ρ - (starRingEnd ℂ) ρ ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at h'
      linarith
    have hzu : zetaResidueUnit (1 - (starRingEnd ℂ) ρ) ≠ 0 := by
      rw [zetaResidueUnit_of_ne hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) hζ
    exact mul_ne_zero hzu (mul_ne_zero (mul_ne_zero hC (mul_ne_zero h1 h2))
      (Complex.exp_ne_zero _))

/-! ## Finite layers below `1` -/

/-- **Every finite layer below `1`.**  For `Re ρ_j ≤ b < 1`, `β ∈ (b, 1)` and
`max(b − 13/30, b/2) < c ≤ 1` there is a two-sided edit of the rational primes with count
`A x + O(x^β)` that is a twin of `ζ` with the layer on `Re s > c`. -/
theorem exists_isEdit_layerTwinOn {ι : Type*} (J : Finset ι) (ρ : ι → ℂ) {b c β : ℝ}
    (hb0 : 0 < b) (hb : b < 1) (hρ : ∀ j ∈ J, (ρ j).re ≤ b) (hc1 : b - 13 / 30 < c)
    (hc2 : b / 2 < c) (hc3 : c ≤ 1) (hβ : b < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      IsFactorTwinOn c (editSystem e) (layerFactor J ρ) := by
  have hρ1 : ∀ j ∈ J, (ρ j).re < 1 := fun j hj => lt_of_le_of_lt (hρ j hj) hb
  have hm : ∀ k : ℕ, 1 ≤ k → |layerTarget J ρ k| ≤ 2 * J.card * (k : ℝ) ^ (-(1 - b)) :=
    fun k hk => abs_layerTarget_le J ρ hρ hk
  have hA : (0 : ℝ) ≤ 2 * J.card := by positivity
  refine ⟨gedit (layerTarget J ρ), isEdit_gedit _,
    editSystem_gedit_count (A := 2 * J.card) (η := 1 - b) hA (by linarith) hm (by linarith) hβ1,
    ?_⟩
  refine isFactorTwinOn_gedit (A := 2 * J.card) (η := 1 - b) hA (by linarith) (by linarith)
    (by linarith) (by linarith) hc3 (layerTarget_zero hρ1) hm
    (Φ₀ := fun s : ℂ => ∑ j ∈ J, (PrimeEdits.zetaRegular (s - (ρ j - 1)) +
      PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) (ρ j) - 1))))
    ?_ (fun s hs => logDeriv_layerFactor_eq J ρ hρ1 hs)
  refine DifferentiableOn.fun_sum fun j _ => ?_
  exact ((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
    (PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _))).differentiableOn

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
