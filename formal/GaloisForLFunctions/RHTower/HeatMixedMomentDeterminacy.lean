import GaloisForLFunctions.RHTower.XiGaussianHeatTwoPrimeSampling
import GaloisForLFunctions.HTGeometry.AtomicMomentDeterminacy

/-!
# Mixed heat moments retain the full countable spectral coupling

Two marginal heat grids can lose the matching between their eigenvalues.
Mixed moments recover arbitrary summable weights on jointly distinct pairs
of nonzero coordinates tending to zero. A generic linear combination avoids
the countably many collisions, reducing the problem to atomic determinacy.
For two distinct prime-log steps, the paired heat coordinate is injective
on the entire complex frequency plane.
-/

open Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- A countable paired packet has a faithful nonzero scalar projection. -/
theorem exists_injective_nonzero_pair_projection {ι : Type*} [Countable ι]
    (x y : ι → ℂ) (hinj : Function.Injective (fun i => (x i, y i)))
    (hnz : ∀ i, x i ≠ 0 ∨ y i ≠ 0) :
    ∃ r : ℂ, Function.Injective (fun i => x i + r * y i) ∧
      ∀ i, x i + r * y i ≠ 0 := by
  let bad : Set ℂ :=
    Set.range (fun i => -x i / y i) ∪
      Set.range (fun ij : ι × ι => (x ij.2 - x ij.1) / (y ij.1 - y ij.2))
  have hbad : bad.Countable := (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r ∉ bad := by
    by_contra h
    push Not at h
    have heq : bad = Set.univ := Set.eq_univ_of_forall h
    exact not_countable_complex (heq ▸ hbad)
  refine ⟨r, ?_, ?_⟩
  · intro i j hij
    by_cases hy : y i = y j
    · apply hinj
      exact Prod.ext (by simpa [hy] using hij) hy
    · exfalso
      apply hr
      right
      refine ⟨(i, j), ?_⟩
      rw [div_eq_iff (sub_ne_zero.mpr hy)]
      linear_combination -hij
  · intro i hi
    by_cases hy : y i = 0
    · rcases hnz i with hx | hy'
      · exact hx (by simpa [hy] using hi)
      · exact hy' hy
    · apply hr
      left
      refine ⟨i, ?_⟩
      rw [div_eq_iff hy]
      linear_combination -hi

/-- Mixed moments converge for summable weights and coordinates tending to zero. -/
theorem summable_pair_moment {c x y : ℕ → ℂ}
    (hc : Summable (fun i => ‖c i‖))
    (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 0)) (m n : ℕ) :
    Summable (fun i => c i * x i ^ m * y i ^ n) := by
  obtain ⟨M, hM⟩ := hx.norm.bddAbove_range
  obtain ⟨N, hN⟩ := hy.norm.bddAbove_range
  have hM0 : 0 ≤ M := (norm_nonneg (x 0)).trans (hM ⟨0, rfl⟩)
  refine Summable.of_norm_bounded (hc.mul_right (M ^ m * N ^ n)) (fun i => ?_)
  simp only [norm_mul, norm_pow]
  calc
    ‖c i‖ * ‖x i‖ ^ m * ‖y i‖ ^ n ≤ ‖c i‖ * M ^ m * N ^ n :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hM ⟨i, rfl⟩) m) (norm_nonneg _))
        (pow_le_pow_left₀ (norm_nonneg _) (hN ⟨i, rfl⟩) n)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg (norm_nonneg _) (pow_nonneg hM0 _))
    _ = ‖c i‖ * (M ^ m * N ^ n) := by ring

/-- All mixed power moments determine arbitrary summable complex weights. -/
theorem coeff_eq_zero_of_pair_moments_vanish {c x y : ℕ → ℂ}
    (hinj : Function.Injective (fun i => (x i, y i)))
    (hnz : ∀ i, x i ≠ 0 ∨ y i ≠ 0)
    (hc : Summable (fun i => ‖c i‖))
    (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 0))
    (hmom : ∀ m n : ℕ, ∑' i, c i * x i ^ m * y i ^ n = 0) :
    ∀ i, c i = 0 := by
  obtain ⟨r, hrinj, hrnz⟩ := exists_injective_nonzero_pair_projection x y hinj hnz
  have hz : Tendsto (fun i => x i + r * y i) atTop (𝓝 0) := by
    simpa using hx.add (hy.const_mul r)
  apply GaloisForLFunctions.HTGeometry.coeff_eq_zero_of_atomicMoments_vanish
    hrinj hrnz hc (by simpa using hz.norm)
  intro k _
  have hexpand (i : ℕ) : c i * (x i + r * y i) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        (c i * x i ^ j * y i ^ (k - j)) * (r ^ (k - j) * (k.choose j : ℂ)) := by
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  simp_rw [hexpand]
  rw [Summable.tsum_finsetSum (fun j _ =>
    (summable_pair_moment hc hx hy j (k - j)).mul_right _)]
  apply Finset.sum_eq_zero
  intro j _
  rw [tsum_mul_right, hmom j (k - j), zero_mul]

/-- The paired prime-log heat coordinate has no spectral aliases. -/
theorem prime_heat_coordinate_pair_injective {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (fun z : ℂ =>
      (Complex.exp (-(Real.log p : ℂ) * z),
        Complex.exp (-(Real.log q : ℂ) * z))) := by
  intro z w heq
  have h₁ := congrArg Prod.fst heq
  have h₂ := congrArg Prod.snd heq
  have hdiff (h : ℝ) (he : Complex.exp (-(h : ℂ) * z) =
      Complex.exp (-(h : ℂ) * w)) : Complex.exp (-(h : ℂ) * (z - w)) = 1 := by
    rw [mul_sub, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
  have him := im_eq_zero_of_two_prime_exp_real hp hq hpq (z - w)
    (by rw [hdiff _ h₁]; rfl) (by rw [hdiff _ h₂]; rfl)
  have hre := Complex.norm_exp_eq_iff_re_eq.mp (congrArg norm h₁)
  have hlog : Real.log p ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero] at hre
    exact (mul_left_cancel₀ (neg_ne_zero.mpr hlog)) hre
  · simpa only [Complex.sub_im, sub_eq_zero] using him

/-- Positive heat coordinates vanish when real frequencies escape to infinity. -/
theorem heat_coordinate_tendsto_zero {w : ℕ → ℂ}
    (hw : Tendsto (fun i => (w i).re) atTop atTop) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun i => Complex.exp (-(h : ℂ) * w i)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  exact Real.tendsto_exp_atBot.comp (hw.const_mul_atTop_of_neg (neg_neg_of_pos hh))

/-- Mixed powers are precisely heat samples on the additive two-step semigroup. -/
theorem heat_mixed_power_identity (w : ℂ) (t h k : ℝ) (m n : ℕ) :
    Complex.exp (-(t : ℂ) * w) * Complex.exp (-(h : ℂ) * w) ^ m *
        Complex.exp (-(k : ℂ) * w) ^ n =
      Complex.exp (-((t + m * h + n * k : ℝ) : ℂ) * w) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Mixed prime-log heat samples determine the full regularized countable packet. -/
theorem coeff_eq_zero_of_mixed_prime_heat_samples {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {c w : ℕ → ℂ} (hw : Function.Injective w)
    (hescape : Tendsto (fun i => (w i).re) atTop atTop) (t : ℝ)
    (hc : Summable (fun i => ‖c i * Complex.exp (-(t : ℂ) * w i)‖))
    (hsamples : ∀ m n : ℕ,
      ∑' i, c i * Complex.exp
        (-((t + m * Real.log p + n * Real.log q : ℝ) : ℂ) * w i) = 0) :
    ∀ i, c i = 0 := by
  have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hq0 : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hzero := coeff_eq_zero_of_pair_moments_vanish
    ((prime_heat_coordinate_pair_injective hp hq hpq).comp hw)
    (fun i => Or.inl (Complex.exp_ne_zero _)) hc
    (heat_coordinate_tendsto_zero hescape hp0)
    (heat_coordinate_tendsto_zero hescape hq0) (fun m n => by
      convert hsamples m n using 1
      apply tsum_congr
      intro i
      rw [mul_assoc (c i), mul_assoc (c i), heat_mixed_power_identity])
  intro i
  exact (mul_eq_zero.mp (hzero i)).resolve_right (Complex.exp_ne_zero _)

end

end RHTower
